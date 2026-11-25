-- Prove2me | Theorems.Thm_PI_QnHermHaar_Gen_pr_of_repOn
-- name    : PI.QnHermHaar.Gen.pr_of_repOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:04.384156+00:00
-- url     : https://prove2.me/theorems/f9882d56-b334-4bb6-8d5b-cc87a9b98f65
-- title:
--   Gen: pr of rep On
-- statement:
--   The Gen construction uses the pr of rep On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L454-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L454-L457

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.QnHermHaar PI.QnHermHaar.Gen
variable {α β : Type*} [MeasurableSpace α]
variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}
variable (hI : IntOn μ ι 𝓕)
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
variable {G}
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)

theorem PI.QnHermHaar.Gen.pr_of_repOn {T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hT : RepOn hI T Φ) (hS : RepOn hI (star T) Ψ)
    {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : pr μ ι (Φ f) h = pr μ ι f (Ψ h) := by sorry
