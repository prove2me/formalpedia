-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_abs_sub_le_of_unit_steps_95b851164d45
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_abs_sub_le_of_unit_steps_95b851164d45
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:55.324951+00:00
-- url     : https://prove2.me/theorems/745bab09-feca-490b-a4aa-6d3d9948b7ed
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel abs sub le of unit steps 95b851164d45: P2 M Ground Theory Heights  Heights Hilbert Samuel abs sub le of unit steps 95b851164d45
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel abs sub le of unit steps 95b851164d45 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel abs sub le of unit steps 95b851164d45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L50-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L50-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_abs_sub_le_of_unit_steps_95b851164d45 (G : (K → ℕ) → ℤ) (A : ℕ) (D : ℝ) (hD : 0 ≤ D) (s : ℕ) :
    ∀ a : K → ℕ, ∑ k, a k = s → (∀ k, A ≤ a k) →
      (∀ (m : K → ℕ) (k : K), (∀ j, A ≤ m j) → ∑ j, m j + 1 ≤ s →
        |((G (m + Pi.single k 1) : ℝ) - G m)| ≤ D) →
      |((G a : ℝ) - G (fun _ => A))| ≤ D * s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«abs_sub_le_of_unit_steps» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_abs_sub_le_of_unit_steps_95b851164d45
