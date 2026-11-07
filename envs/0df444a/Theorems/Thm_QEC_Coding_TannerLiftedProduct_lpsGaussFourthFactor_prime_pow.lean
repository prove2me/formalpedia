-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGaussFourthFactor_prime_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsGaussFourthFactor_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:55.985917+00:00
-- url     : https://prove2.me/theorems/4efadc20-0979-4a5b-83e0-4dae276efff0
-- title:
--   Tanner Lifted Product: lps Gauss Fourth Factor prime pow
-- statement:
--   Both prime-power evaluations agree with the residue factor, including exponents zero and one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L453-L471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L453-L471

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsGaussFourthFactor_prime_pow (p e : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsUnit (a:ZMod (p^e))) :
    lpsUnaryQuadraticGauss a (p^e)^4=
      (lpsGaussFourthFactor (p^e):ℂ)*((p^e:ℕ):ℂ)^2 := by sorry
