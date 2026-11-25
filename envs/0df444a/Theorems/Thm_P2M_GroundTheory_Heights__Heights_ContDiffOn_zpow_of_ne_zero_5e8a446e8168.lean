-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ContDiffOn_zpow_of_ne_zero_5e8a446e8168
-- name    : P2M_GroundTheory_Heights__Heights_ContDiffOn_zpow_of_ne_zero_5e8a446e8168
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:48.91985+00:00
-- url     : https://prove2.me/theorems/8c8aeb1b-84b5-45ce-879b-50cc0afc54f3
-- title:
--   P2 M Ground Theory Heights  Heights Cont Diff On zpow of ne zero 5e8a446e8168: P2 M Ground Theory Heights  Heights Cont Diff On zpow of ne zero 5e8a446e8168
-- statement:
--   The P2 M Ground Theory Heights  Heights Cont Diff On zpow of ne zero 5e8a446e8168 construction uses the P2 M Ground Theory Heights  Heights Cont Diff On zpow of ne zero 5e8a446e8168 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemPointsOfGeneratorsVanish.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemPointsOfGeneratorsVanish.lean#L25-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemPointsOfGeneratorsVanish
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
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ContDiffOn_zpow_of_ne_zero_5e8a446e8168 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ContDiffOn ℝ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) :
    ContDiffOn ℝ ∞ (fun x ↦ f x ^ m) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ContDiffOn».«zpow_of_ne_zero» := P2M_GroundTheory_Heights__Heights_ContDiffOn_zpow_of_ne_zero_5e8a446e8168
