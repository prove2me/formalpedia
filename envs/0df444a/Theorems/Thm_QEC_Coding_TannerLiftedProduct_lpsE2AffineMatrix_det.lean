-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:26.643738+00:00
-- url     : https://prove2.me/theorems/9be42af9-48df-43e9-8986-76c87298e34d
-- title:
--   Tanner Lifted Product: lps E2 Affine Matrix det
-- statement:
--   The genuine affine determinant is the positive dilation used by the slash normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L143-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L143-L146

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_det (m : ℕ) (hm : 0<m) (r : ℝ) :
    (lpsE2AffineMatrix m hm r).det.val=(m:ℝ) := by sorry
