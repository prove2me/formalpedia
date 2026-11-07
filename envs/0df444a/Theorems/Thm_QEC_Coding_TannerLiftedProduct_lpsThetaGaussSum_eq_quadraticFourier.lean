-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaGaussSum_eq_quadraticFourier
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_eq_quadraticFourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:55.267585+00:00
-- url     : https://prove2.me/theorems/8959f087-20e7-4d14-a830-d4d40d15775a
-- title:
--   Tanner Lifted Product: lps Theta Gauss Sum eq quadratic Fourier
-- statement:
--   Absolute summability permits the actual finite/infinite Fourier interchange.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L109-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L109-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_eq_quadraticFourier (a : ℤ) (N : ℕ) [NeZero N] (z : ℂ) (hz : 0 < z.im) :
    lpsThetaGaussSum a N z =
      ∑' n : ℤ, lpsQuadraticFourier N (a:ZMod N) (n:ZMod N) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z) := by sorry
