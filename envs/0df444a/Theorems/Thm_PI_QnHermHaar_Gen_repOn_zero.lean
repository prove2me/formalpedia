-- Prove2me | Theorems.Thm_PI_QnHermHaar_Gen_repOn_zero
-- name    : PI.QnHermHaar.Gen.repOn_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:25.494791+00:00
-- url     : https://prove2.me/theorems/4be4a9b2-e58d-4242-ad67-b3de0ecfaa13
-- title:
--   Gen: rep On zero
-- statement:
--   The Gen construction uses the rep On zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L410-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L410-L414

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

theorem PI.QnHermHaar.Gen.repOn_zero : RepOn hI (0 : A hI) (fun _ => 0) := by sorry
