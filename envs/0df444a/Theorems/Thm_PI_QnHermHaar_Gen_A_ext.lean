-- Prove2me | Theorems.Thm_PI_QnHermHaar_Gen_A_ext
-- name    : PI.QnHermHaar.Gen.A_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:58:35.843797+00:00
-- url     : https://prove2.me/theorems/10fe7a16-0d81-4312-bc20-98fe07b38f89
-- title:
--   Gen: A ext
-- statement:
--   The Gen construction uses the A ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L239-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L239-L245

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

theorem PI.QnHermHaar.Gen.A_ext {S T : A hI}
    (h : ∀ f ∈ 𝓕, (S : Module.End ℂ (X hI)) (mk' hI f) = (T : Module.End ℂ (X hI)) (mk' hI f)) : S = T := by sorry
