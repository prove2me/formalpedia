-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_tendsto_finset_sum_zero_a6939454619a
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_tendsto_finset_sum_zero_a6939454619a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:28.21077+00:00
-- url     : https://prove2.me/theorems/7d8bf088-505f-490d-8935-15ebb35017a7
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff tendsto finset sum zero a6939454619a: P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff tendsto finset sum zero a6939454619a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff tendsto finset sum zero a6939454619a construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Diff tendsto finset sum zero a6939454619a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightDiffLemmas.lean#L94-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_tendsto_finset_sum_zero_a6939454619a {ι α : Type*} {l : Filter α} (s : Finset ι) (f : ι → α → ℝ)
    (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 0)) : Tendsto (fun a => ∑ i ∈ s, f i a) l (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightDiff».«tendsto_finset_sum_zero» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_tendsto_finset_sum_zero_a6939454619a
