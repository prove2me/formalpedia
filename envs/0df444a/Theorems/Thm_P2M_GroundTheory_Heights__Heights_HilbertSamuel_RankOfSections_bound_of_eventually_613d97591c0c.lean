-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_bound_of_eventually_613d97591c0c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_bound_of_eventually_613d97591c0c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:50.388943+00:00
-- url     : https://prove2.me/theorems/49e2ecd8-6472-4b47-adf3-33303bfad75e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections bound of eventually 613d97591c0c: P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections bound of eventually 613d97591c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections bound of eventually 613d97591c0c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections bound of eventually 613d97591c0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRankOfSections.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRankOfSections.lean#L59-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_bound_of_eventually_613d97591c0c (f : ℕ → ℝ) (r : ℝ) (a₀ : ℕ) (C : ℝ)
    (h : ∀ n, a₀ ≤ n → |f n| ≤ C * ((n : ℝ) + 1) ^ r) :
    ∃ C' : ℝ, ∀ n : ℕ, |f n| ≤ C' * ((n : ℝ) + 1) ^ r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RankOfSections».«bound_of_eventually» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_bound_of_eventually_613d97591c0c
