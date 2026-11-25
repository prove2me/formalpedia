-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_pointX_isBasisOf_17e40af1f27a
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_pointX_isBasisOf_17e40af1f27a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:30.928292+00:00
-- url     : https://prove2.me/theorems/789c44c2-1e45-4cad-8521-8e9fd46b2ad0
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula point X is Basis Of 17e40af1f27a: P2 M Ground Theory Heights  Heights Key Formula point X is Basis Of 17e40af1f27a
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula point X is Basis Of 17e40af1f27a construction uses the P2 M Ground Theory Heights  Heights Key Formula point X is Basis Of 17e40af1f27a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/ResidueChartModel.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/ResidueChartModel.lean#L76-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman (Poly GradedMod Xprod polyPiece polyGraded)
noncomputable section
attribute [instance] ResidueChartModel.grp ResidueChartModel.modP ResidueChartModel.modC
  ResidueChartModel.tower

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_pointX_isBasisOf_17e40af1f27a : pointForm.IsBasisOf 3 pointX := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«pointX_isBasisOf» := P2M_GroundTheory_Heights__Heights_KeyFormula_pointX_isBasisOf_17e40af1f27a
