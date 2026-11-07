-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_odd_mask_frequency
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_odd_mask_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:23.32343+00:00
-- url     : https://prove2.me/theorems/dc001e76-b412-4790-9a0a-54af6f326c5e
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier odd mask frequency
-- statement:
--   Two actual units complete the odd mask frequency with zero quadratic phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L241-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L241-L272

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_odd_mask_frequency (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (a : ℤ) (ha : IsUnit (a:ZMod N))
    (h2 : IsUnit (2:ZMod N)) (j : ℤ) :
    lpsQuadraticFourier N (a:ZMod N) (((d:ℤ)*(k:ℤ)*j:ℤ):ZMod N) =
      lpsUnaryQuadraticGauss a N := by sorry
