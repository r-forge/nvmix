## 0. Auxilary functions ##################################


#' Transform a vector of correlations to symmetric correlation matrix
#' @param rho vector of correlations
#' @return symmetric matrix of correlations
#' @author Erik Hintz with code from Yoshiba (2018)
rhoToOmega <- function(rho){
   dim <- (sqrt(8*length(rho)+1)+1)/2 
   Omega <- diag(1/2,dim)
   Omega[lower.tri(Omega)] <- rho
   Omega <- Omega + t(Omega)
   Omega
}

## 1.1. t copula case ##########################################################

#' Transform internal to original parameters (t case)
#' @param para vector of parameters 
#' @return 2-list with the correlation matrix and dof 'nu'  
#' @author Erik Hintz with code from Yoshiba (2018)
int_to_org_pars_t <- function(par){
   lengthpar <- length(par)
   nu <- par[lengthpar] # grab dof (last element)
   theta <- par[-lengthpar] 
   dim <- (1 + sqrt(1 + 8*(lengthpar - 1)))/2
   LTR <- diag(dim)
   LTR[-1,1] <- cos(theta[1:(dim-1)])
   cumsin <- sin(theta[1:(dim-1)])
   if(dim > 2){
      for(j in 2:(dim-1)){
         LTR[j,j] <- cumsin[1]
         k <- (j - 1)*(dim - j/2) + 1
         thj <- theta[k:(k+dim-j-1)]
         cumsin <- cumsin[-1]
         LTR[((j+1):dim),j] <- cumsin*cos(thj)
         cumsin <- cumsin * sin(thj) 
      } 
   }
   LTR[dim,dim] <- cumsin[1]
   Omega <- LTR %*% t(LTR)
   ## Return
   list(rho = Omega[lower.tri(Omega)], nu = nu)
}

#' Transform original parameters to internal parameters (t case)
#' @param rho original 'correlations'
#' @param gamma skewness 
#' @param nu degrees of freedom
#' @return vector with transformed parameters (ANGLES -- GAMMA -- DF)
#' @author Erik Hintz with code from Yoshiba (2018)
org_to_int_pars_t <- function(rho, nu){
   R <- rhoToOmega(rho)
   LTR <- t(chol(R))
   dim <- nrow(LTR)
   theta <- acos(LTR[2:dim, 1])
   cumsin <- sin(theta)[-1]
   if(dim > 2){
      for(j in 2:(dim-1)){
         thj <- acos(LTR[(j+1):dim,j]/cumsin);
         theta <- c(theta,thj);
         cumsin <- (cumsin*sin(thj))[-1];
      } 
   }
   ## Return
   c(theta, nu)
}


## 1.2. skew-t copula case #####################################################

#' Transform internal to original parameters (skew t case)
#' @param par vector of parameters 
#' @return 3-list with the correlation matrix, dof 'nu' and 'gamma' 
#' @author Erik Hintz with code from Yoshiba (2018)
int_to_org_pars_st <- function(par){
   ntheta <- length(par) - 2 
   dim <- (1 + sqrt(1 + 8*ntheta))/2
   theta <- par[1:ntheta]
   LTR <- diag(dim)
   LTR[-1,1] <- cos(theta[1:(dim-1)])
   cumsin <- sin(theta[1:(dim-1)])
   if(dim > 2){
      for(j in 2:(dim-1)){
         LTR[j,j] <- cumsin[1]
         k <- (j - 1)*(dim - j/2) + 1
         thj <- theta[k:(k+dim-j-1)]
         cumsin <- cumsin[-1]
         LTR[((j+1):dim),j] <- cumsin*cos(thj)
         cumsin <- cumsin * sin(thj) 
      } 
   }
   LTR[dim,dim] <- cumsin[1]
   Omega <- LTR %*% t(LTR)
   gamma <- par[ntheta+2] 
   nu <- par[ntheta+1]
   ## Return
   list(rho = Omega[lower.tri(Omega)], nu = nu, gamma = gamma)
}

#' Transform original parameters to internal parameters (skew-t case)
#' @param rho original 'correlations'
#' @param gamma skewness 
#' @param nu degrees of freedom
#' @return vector with transformed parameters (ANGLES -- GAMMA -- DF)
#' @author Erik Hintz with code from Yoshiba (2018)
org_to_int_pars_st <- function(rho, gamma, nu){
   R <- rhoToOmega(rho)
   LTR <- t(chol(R))
   dim <- nrow(LTR)
   theta <- acos(LTR[2:dim, 1])
   cumsin <- sin(theta)[-1]
   if(dim > 2){
      for(j in 2:(dim-1)){
         thj <- acos(LTR[(j+1):dim,j]/cumsin);
         theta <- c(theta,thj);
         cumsin <- (cumsin*sin(thj))[-1];
      } 
   }
   ## Return
   c(theta, nu, gamma)
}


#' Fit P matrix of skew-t copula using an EM-like algorithm
#' @param u (n, d) data-matrix (must be in (0,1))
#' @param pseudoskewt (n, d) matrix of pseudo-observations 
#' @param nu dof parameter
#' @param gamma skewness vector
#' @param P starting guess for P
#' @param P_inv inverse of P 
#' @param ldet log(det(P))
#' @param report.ll logical if log-lik before and after should be reported
#' @param P_maxiter maximum number of iterations for 'P' updates
#' @param P_tol relative convergence tolerance for elements in 'P'
#' @return 5-list with 'P_next', 'P_next_inv', 'ldet_next', 'll' 
#' @author Erik Hintz 
fitscaleskewtEM <- function(u, pseudoskewt = NULL, nu, gamma, P, P_inv = NULL,
                            ldet = NULL,
                            report.ll = FALSE, P_maxiter = 50, P_tol, ...){
   if(!is.matrix(u)) u <- cbind(u)
   d <- ncol(u)
   n <- nrow(u)
   if(is.null(P_inv)){
      P_inv <- pd.solve(P, log.det = TRUE)
      ldet <- attr(P_inv, "log.det")
   } else stopifnot(is.numeric(ldet))
   stopifnot(all(gamma == 0)) # only t-case
   if(!is.null(pseudoskewt)){
      ## Most basic check 
      if(!is.matrix(pseudoskewt)) pseudoskewt <- cbind(pseudoskewt)
   } else {
      ## Compute pseudo-observations 
      pseudoskewt <- matrix(qt(as.vector(u), df = nu), ncol = d) 
   }
   pseudoskewt_mean_colvec <- matrix(colMeans(pseudoskewt), ncol = 1)
   ## Compute starting ll
   ll <- if(!report.ll) NA else
      sum(dStudentcopula(u, scale = P, df = nu, log = TRUE))
   ## Update 'scale'
   P_converged <- FALSE
   P_iter <- 1
   # if(any(gamma != 0)){
   #    while(!P_converged & P_iter < P_maxiter){
   #       mahaXplusnu <- mahalanobis(pseudoskewt, center = FALSE, cov = P_inv,
   #                                  inverted = TRUE) + nu
   #       mahagam <- mahalanobis(gamma, center = FALSE, cov = P_inv,
   #                              inverted = TRUE)
   #       besselarg <- sqrt(mahaXplusnu * mahagam)
   #       bessel1 <- besselK(besselarg, nu = (-(d + nu)/2 + 1))
   #       bessel2 <- besselK(besselarg, nu = (-(d + nu)/2))
   #       bessel3 <- besselK(besselarg, nu = (-(d + nu)/2 - 1))
   #       delta <- 1/sqrt(mahaXplusnu/mahagam) * bessel3 / bessel2
   #       eta_bar <- sum(sqrt(mahaXplusnu/mahagam) * bessel1 / bessel2)/n
   #       P_next <- as.matrix(Matrix::nearPD(
   #          (crossprod(sqrt(delta)*pseudoskewt)/n + eta_bar * tcrossprod(gamma)
   #           - tcrossprod(pseudoskewt_mean_colvec, gamma) -
   #              t(tcrossprod(pseudoskewt_mean_colvec, gamma))))$mat)
   #       P_next_inv <- pd.solve(P_next, log.det = TRUE)
   #       ldet <- attr(P_next_inv, "log.det")
   #       reldiff_P <- max(abs(P_next - P)/P)
   #       P_converged <- (reldiff_P < P_tol)
   #       P_iter <- P_iter + 1
   #       P <- P_next
   #       P_inv <- P_next_inv
   #    }
   
   ## Standard multivariate t setting
   while(!P_converged & P_iter < P_maxiter){
      maha2_current <- mahalanobis(pseudoskewt, center = FALSE, 
                                   cov = P_inv, inverted = TRUE)
      weights <- (nu + d) / (nu + maha2_current)
      P_next <- as.matrix(nearPD(
         crossprod(sqrt(weights)*pseudoskewt)/n, corr = TRUE)$mat) 
      P_next_inv <- pd.solve(P_next, log.det = TRUE)
      ldet <- attr(P_next_inv, "log.det")
      reldiff_P <- max(abs(P_next - P)/P)
      P_converged <- (reldiff_P < P_tol)
      P_iter <- P_iter + 1
      P <- P_next
      P_inv <- P_next_inv
   }
   P_next_inv <- pd.solve(P_next, log.det = TRUE)
   ldet_next <- attr(P_next_inv, "log.det")
   ## Compute log-density
   if(report.ll){
      ll_next <- sum(dStudentcopula(u, scale = P_next, df = nu, log = TRUE))
      ll <- c(ll, ll_next)
      names(ll) <- c("initial", "terminal")
   }
   ## Return
   list(P_next = P_next, P_next_inv = P_next_inv, ldet_next = ldet_next, 
        ll = ll)
}
