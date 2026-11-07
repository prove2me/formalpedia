-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_zero_eq_Gauss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:35.926592+00:00
-- url     : https://prove2.me/theorems/7c4a5d7a-c7da-4cc9-bbc7-4914e46f6dc3
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier zero eq Gauss
-- statement:
--   Zero frequency is the existing actual Fin-indexed Gauss sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L84-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L84-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_zero_eq_Gauss (N : ℕ) [NeZero N] (a : ℤ) :
    lpsQuadraticFourier N (a:ZMod N) 0 = lpsUnaryQuadraticGauss a N := by sorry
