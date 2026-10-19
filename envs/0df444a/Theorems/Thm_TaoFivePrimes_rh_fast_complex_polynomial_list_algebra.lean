-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_complex_polynomial_list_algebra
-- name    : TaoFivePrimes.rh_fast_complex_polynomial_list_algebra
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:31:28.669549+00:00
-- url     : https://prove2.me/theorems/64700191-ae0b-4765-8280-a5f5b3d7b7eb
-- title:
--   TaoFivePrimes.rh_fast_complex_polynomial_list_algebra
-- statement:
--   Complex coefficient-list addition, convolution and division agree with the corresponding polynomial operations.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexPolynomialLists
open Complex

theorem TaoFivePrimes.rh_fast_complex_polynomial_list_algebra (xs ys:List ℂ) (n:Nat) :
 RHFastComplexPoly.polynomial (RHFastComplexPoly.addList xs ys)=
   RHFastComplexPoly.polynomial xs+RHFastComplexPoly.polynomial ys ∧
 RHFastComplexPoly.polynomial (RHFastComplexPoly.mulList xs ys)=
   RHFastComplexPoly.polynomial xs*RHFastComplexPoly.polynomial ys ∧
 RHFastComplexPoly.polynomial (RHFastComplexPoly.divideList xs n)=
   RHFastComplexPoly.polynomial xs*Polynomial.C ((n:ℂ)⁻¹) := by sorry
