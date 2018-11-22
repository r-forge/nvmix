/* Register routines with R ***************************************************/

#include <R.h>
#include <Rinternals.h>
#include <R_ext/Rdynload.h>
#include <Rmath.h>

#include "eval_nvmix_integral.h"
#include "eval_dnvmix_integrand.h"

static const R_CallMethodDef callMethods[] = {
    {"eval_nvmix_integral", (DL_FUNC) &eval_nvmix_integral, 8},
    {"eval_dnvmix_integrand", (DL_FUNC) &eval_dnvmix_integrand, 6},
    {NULL, NULL, 0}
};

void R_init_nvmix(DllInfo *dll)
{
    R_registerRoutines(dll, NULL, callMethods, NULL, NULL); /* s. WRE (2015, Section 5.4) */
    R_useDynamicSymbols(dll, FALSE);
}
