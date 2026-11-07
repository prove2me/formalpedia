-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_mask_sum_modulus
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_mask_sum_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:32.022318+00:00
-- url     : https://prove2.me/theorems/7cea4666-8565-49d7-89ab-bf2cc01983bf
-- title:
--   Tanner Lifted Product: lps Quadratic Gauss mask sum modulus
-- statement:
--   The proved mask projection with an explicitly identified modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L275-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L275-L280

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_mask_sum_modulus (N d m : ℕ) [NeZero N] [NeZero d] [NeZero m]
    (hN : N=d*m) (a : ℤ) :
    (∑ j : Fin d, lpsQuadraticFourier N (a:ZMod N) (((m:ℤ)*j.val:ℤ):ZMod N)) =
      lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N := by sorry
