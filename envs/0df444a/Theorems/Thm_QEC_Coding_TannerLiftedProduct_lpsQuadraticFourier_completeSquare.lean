-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_completeSquare
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_completeSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:25.088584+00:00
-- url     : https://prove2.me/theorems/8758b936-e1b2-421d-b3a7-87ff3e036574
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier complete Square
-- statement:
--   Translation of the finite cyclic index completes the square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L29-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L29-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_completeSquare (N : ℕ) [NeZero N] (a t : ZMod N) :
    lpsQuadraticFourier N a (2*a*t) =
      ZMod.stdAddChar (-a*t^2) * lpsQuadraticFourier N a 0 := by sorry
