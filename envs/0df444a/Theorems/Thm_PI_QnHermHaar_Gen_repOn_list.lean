-- Prove2me | Theorems.Thm_PI_QnHermHaar_Gen_repOn_list
-- name    : PI.QnHermHaar.Gen.repOn_list
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:01.779668+00:00
-- url     : https://prove2.me/theorems/b68abb33-966d-5153-b97b-21cebc7a4b1b
-- title:
--   Gen: rep On list
-- statement:
--   The Gen construction uses the rep On list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L443-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L443-L452

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

theorem PI.QnHermHaar.Gen.repOn_list (t : ℕ) (F : Fin t → A hI) (Φ : Fin t → (β → ℂ) → β → ℂ)
    (h : ∀ k, RepOn hI (F k) (Φ k)) :
    RepOn hI (List.ofFn F).prod (fun f => (List.ofFn Φ).foldr (fun T h => T h) f) := by sorry
