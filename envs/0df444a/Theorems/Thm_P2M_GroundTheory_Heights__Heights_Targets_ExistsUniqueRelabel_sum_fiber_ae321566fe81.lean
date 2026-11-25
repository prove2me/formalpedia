-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sum_fiber_ae321566fe81
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sum_fiber_ae321566fe81
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:33.9082+00:00
-- url     : https://prove2.me/theorems/11fcfad7-96b9-4c59-b7b3-7c24b0731cba
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel sum fiber ae321566fe81: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel sum fiber ae321566fe81
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel sum fiber ae321566fe81 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel sum fiber ae321566fe81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L104-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sum_fiber_ae321566fe81 {M : Type*} [AddCommMonoid M] [DecidableEq K] (g : (Σ k, ι k) → M) (k : K) :
    ∑ i, g ⟨k, i⟩ = ∑ p : Σ k, ι k, if p.1 = k then g p else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«sum_fiber» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sum_fiber_ae321566fe81
