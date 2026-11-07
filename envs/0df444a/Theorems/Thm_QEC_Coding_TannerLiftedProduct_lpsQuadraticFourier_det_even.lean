-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_det_even
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_det_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:59.486505+00:00
-- url     : https://prove2.me/theorems/7f288334-ff00-4b03-b93e-5ad272cec617
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier det even
-- statement:
--   Determinant one determines the remaining quadratic coefficient phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L156-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L156-L174

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_det_even (N s : ℕ) [NeZero N] (a b d j : ℤ)
    (hdet : a*d-b*(N:ℤ)=1) :
    lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) ((2*(s:ℤ)*j:ℤ):ZMod N) =
      ZMod.stdAddChar (((-(s:ℤ)*d*j^2:ℤ):ZMod N))*lpsUnaryQuadraticGauss ((s:ℤ)*a) N := by sorry
