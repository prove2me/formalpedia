-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tendsto_of_forall_local_62c374128f22
-- name    : P2M_GroundTheory_Heights__Heights_tendsto_of_forall_local_62c374128f22
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:43.480447+00:00
-- url     : https://prove2.me/theorems/daf61895-8d12-4829-861e-c1708715660e
-- title:
--   P2 M Ground Theory Heights  Heights tendsto of forall local 62c374128f22: P2 M Ground Theory Heights  Heights tendsto of forall local 62c374128f22
-- statement:
--   The P2 M Ground Theory Heights  Heights tendsto of forall local 62c374128f22 construction uses the P2 M Ground Theory Heights  Heights tendsto of forall local 62c374128f22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/LocalLimitGlue.lean#L9-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/LocalLimitGlue.lean#L9-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology Set Function
open scoped ContDiff Manifold

theorem P2M_GroundTheory_Heights__Heights_tendsto_of_forall_local_62c374128f22 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι} (T : ι → (E → ℝ) → ℝ) (L : (E → ℝ) → ℝ)
    (hT : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → ∀ᶠ ε in l, T ε (f + g) = T ε f + T ε g)
    (hL : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → L (f + g) = L f + L g)
    (hloc : ∀ p : E, ∃ N ∈ 𝓝 p, ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ N → Tendsto (fun ε => T ε f) l (𝓝 (L f)))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε => T ε f) l (𝓝 (L f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tendsto_of_forall_local» := P2M_GroundTheory_Heights__Heights_tendsto_of_forall_local_62c374128f22
