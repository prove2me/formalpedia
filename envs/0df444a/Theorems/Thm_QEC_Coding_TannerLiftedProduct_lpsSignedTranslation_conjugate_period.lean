-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_conjugate_period
-- name    : QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_conjugate_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:30.629921+00:00
-- url     : https://prove2.me/theorems/8b7e654b-3ce9-4f70-99fc-847be5a6b1db
-- title:
--   Tanner Lifted Product: lps Signed Translation conjugate period
-- statement:
--   Conjugating a period by a genuine signed translation leaves that period unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L36-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L36-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_conjugate_period (g : GL (Fin 2) ℝ) (x t : ℝ)
    (hg : g = Matrix.GeneralLinearGroup.upperRightHom x ∨
      g = -Matrix.GeneralLinearGroup.upperRightHom x) :
    g * Matrix.GeneralLinearGroup.upperRightHom t * g⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom t := by sorry
