-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteField_square_sum_eq_gauss
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteField_square_sum_eq_gauss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:45.097006+00:00
-- url     : https://prove2.me/theorems/ad41819d-ec9c-4ad9-b66d-108ec57ebdbd
-- title:
--   Tanner Lifted Product: lps Finite Field square sum eq gauss
-- statement:
--   Actual square-root fibers identify the quadratic additive sum with the character Gauss sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L27-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L27-L43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteField_square_sum_eq_gauss (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x^2)) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by sorry
