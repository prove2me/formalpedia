-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaGaussSum_scalar
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:41.123552+00:00
-- url     : https://prove2.me/theorems/fdc899ee-a6ca-48c3-906b-dd9e6e0af048
-- title:
--   Tanner Lifted Product: lps Theta Gauss Sum scalar
-- statement:
--   Reindex the actual supported series and cancel the exact determinant phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L177-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L177-L224

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_scalar (N s k : ℕ) [NeZero N] (hs : 0 < s) (hk : 0 < k)
    (hN : N=4*s*k) (a b d : ℤ) (hdet : a*d-b*(N:ℤ)=1)
    (z : ℂ) (hz : 0 < z.im) :
    lpsThetaGaussSum ((s:ℤ)*a) N ((z+(d:ℂ)/(N:ℂ))/(2*(s:ℂ))) =
      lpsUnaryQuadraticGauss ((s:ℤ)*a) N * jacobiTheta (2*(s:ℂ)*z) := by sorry
