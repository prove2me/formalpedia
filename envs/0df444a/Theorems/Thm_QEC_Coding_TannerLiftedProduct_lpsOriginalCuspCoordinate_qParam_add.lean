-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_qParam_add
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_qParam_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:52.096097+00:00
-- url     : https://prove2.me/theorems/cc21f4e4-634d-4cd9-9ad8-d694abc42ffd
-- title:
--   Tanner Lifted Product: lps Original Cusp Coordinate q Param add
-- statement:
--   Literal exponential algebra computes the constant phase of a translated cusp coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L138-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L138-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_qParam_add (w : ℝ) (z u : ℂ) :
    Function.Periodic.qParam w (z + u) =
      Function.Periodic.qParam w u * Function.Periodic.qParam w z := by sorry
