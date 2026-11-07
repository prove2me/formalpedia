-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_even_support
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_even_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:47.796869+00:00
-- url     : https://prove2.me/theorems/e1ea4ba7-78d3-4d5d-9f67-1a6771345c5e
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier even support
-- statement:
--   An explicit cyclic translation leaves support only on multiples of 2*s.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L127-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L127-L153

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_even_support (N s k : ℕ) [NeZero N] (hN : N=4*s*k)
    (hk : 0 < k) (a n : ℤ) (hn : ¬ (2*(s:ℤ)) ∣ n) :
    lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) = 0 := by sorry
