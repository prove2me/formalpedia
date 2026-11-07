-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_of_translation
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_zero_of_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:19.803695+00:00
-- url     : https://prove2.me/theorems/6d3a674c-671b-473b-b71d-9745aa25c0b6
-- title:
--   Tanner Lifted Product: lps Quadratic Fourier zero of translation
-- statement:
--   A genuine nontrivial phase under an invariant quadratic translation forces vanishing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L44-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L44-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_zero_of_translation (N : ℕ) [NeZero N] (a n t : ZMod N)
    (hlinear : 2*a*t=0) (hquadratic : a*t^2=0) (hn : n*t≠0) :
    lpsQuadraticFourier N a n=0 := by sorry
