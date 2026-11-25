-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_iff_053461e9f345
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_iff_053461e9f345
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:13.002144+00:00
-- url     : https://prove2.me/theorems/a7806f09-2a63-45b8-b625-4ea0e040fc5c
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Relevant iff 053461e9f345: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Relevant iff 053461e9f345
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Relevant iff 053461e9f345 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Relevant iff 053461e9f345 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L96-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_iff_053461e9f345 (W : Ideal (MRingOver F ι)) :
    IsRelevant W ↔ ∀ k, ∃ p : Σ k, ι k, p.1 = k ∧ (X p : MRingOver F ι) ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«isRelevant_iff» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_iff_053461e9f345
