-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_commute_period
-- name    : QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_commute_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:26.487206+00:00
-- url     : https://prove2.me/theorems/66084246-77ed-44d3-84b9-34b8e799f5d9
-- title:
--   Tanner Lifted Product: lps Signed Translation commute period
-- statement:
--   A genuine signed cusp translation commutes with every strict-period translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L23-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L23-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_commute_period (g : GL (Fin 2) ℝ) (x t : ℝ)
    (hg : g = Matrix.GeneralLinearGroup.upperRightHom x ∨
      g = -Matrix.GeneralLinearGroup.upperRightHom x) :
    g * Matrix.GeneralLinearGroup.upperRightHom t =
      Matrix.GeneralLinearGroup.upperRightHom t * g := by sorry
