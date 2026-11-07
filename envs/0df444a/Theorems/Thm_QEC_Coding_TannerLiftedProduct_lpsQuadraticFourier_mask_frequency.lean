-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_mask_frequency
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_mask_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:56.193136+00:00
-- url     : https://prove2.me/theorems/ebbf910a-c8da-46b8-93c0-9dc403e0f9b3
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier mask frequency
-- statement:
--   The determinant unit completes each mask frequency with zero quadratic phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L23-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L23-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_mask_frequency (N d k : ℕ) [NeZero N]
    (hN : N=4*d^2*k) (a b u j : ℤ) (hdet : a*u-b*(N:ℤ)=1) :
    lpsQuadraticFourier N (a:ZMod N) ((4*(d:ℤ)*(k:ℤ)*j:ℤ):ZMod N) =
      lpsUnaryQuadraticGauss a N := by sorry
