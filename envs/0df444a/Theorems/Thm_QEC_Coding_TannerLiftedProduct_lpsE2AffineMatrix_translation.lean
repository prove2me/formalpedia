-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_translation
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:27.208965+00:00
-- url     : https://prove2.me/theorems/0277a95f-8e6c-4cc3-a6f3-f528ae8fdf0e
-- title:
--   Tanner Lifted Product: lps E2 Affine Matrix translation
-- statement:
--   Actual affine actions identify a translation after dilation with the single affine action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L226-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L226-L231

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_translation (m : ℕ) (hm : 0<m) (r : ℝ) (z : ℍ) :
    r +ᵥ (lpsE2AffineMatrix m hm 0 • z) = lpsE2AffineMatrix m hm r • z := by sorry
