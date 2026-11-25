-- Prove2me | Theorems.Thm_PositivityTheory_AdelicQuotientData_SeparatedThetaSum_sep_sum
-- name    : PositivityTheory.AdelicQuotientData.SeparatedThetaSum.sep_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:41.03873+00:00
-- url     : https://prove2.me/theorems/41cdcc7e-b4b8-4f86-ace0-1cd62809ce25
-- title:
--   Separated Theta Sum: sep sum
-- statement:
--   The Separated Theta Sum construction uses the sep sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/JacquetShalikaRigidity/SepSum.lean#L9-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/JacquetShalikaRigidity/SepSum.lean#L9-L73

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_JacquetShalikaRigidity_SepSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.AdelicQuotientData PositivityTheory.AdelicQuotientData.SeparatedThetaSum

theorem PositivityTheory.AdelicQuotientData.SeparatedThetaSum.sep_sum (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∀ P : Finset X, (∀ p ∈ P, ρ ≤ ‖p‖) →
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ ≤ ‖p - q‖) →
      ∑ p ∈ P, ((1 + ‖p‖) ^ (Module.finrank ℝ X + 1))⁻¹ ≤ C * (ρ ^ Module.finrank ℝ X)⁻¹ := by sorry
