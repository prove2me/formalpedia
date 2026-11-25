-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BlowUpChart_hypotheses_inhabited_04be7bb79312
-- name    : P2M_GroundTheory_Heights__Heights_Model_BlowUpChart_hypotheses_inhabited_04be7bb79312
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:48:32.200644+00:00
-- url     : https://prove2.me/theorems/e07a14c6-b6ff-4de5-b82e-a65cd844c203
-- title:
--   P2 M Ground Theory Heights  Heights Model Blow Up Chart hypotheses inhabited 04be7bb79312: P2 M Ground Theory Heights  Heights Model Blow Up Chart hypotheses inhabited 04be7bb79312
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Blow Up Chart hypotheses inhabited 04be7bb79312 construction uses the P2 M Ground Theory Heights  Heights Model Blow Up Chart hypotheses inhabited 04be7bb79312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L472-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L472-L477

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_BlowUpChart_hypotheses_inhabited_04be7bb79312 :
    Ideal.span (Set.range ![(2 : ℤ_[2])]) = IsLocalRing.maximalIdeal ℤ_[2] ∧
      ∃ j, ![(2 : ℤ_[2])] j ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«BlowUpChart».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_BlowUpChart_hypotheses_inhabited_04be7bb79312
