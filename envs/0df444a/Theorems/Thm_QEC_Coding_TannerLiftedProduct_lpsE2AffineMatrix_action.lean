-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:33.22905+00:00
-- url     : https://prove2.me/theorems/f89ade22-b229-4df4-aabb-a29205bfd353
-- title:
--   Tanner Lifted Product: lps E2 Affine Matrix action
-- statement:
--   The actual positive-determinant action is the complex affine map m z plus r.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L153-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L153-L156

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_action (m : ℕ) (hm : 0<m) (r : ℝ) (z : ℍ) :
    ((lpsE2AffineMatrix m hm r • z:ℍ):ℂ)=(m:ℂ)*(z:ℂ)+(r:ℂ) := by sorry
