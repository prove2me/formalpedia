-- Prove2me | Theorems.Thm_P2M_PI_QnHermHaar_Gen_mk__zero_2a7bf532d2bf
-- name    : P2M_PI_QnHermHaar_Gen_mk__zero_2a7bf532d2bf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:57:05.004034+00:00
-- url     : https://prove2.me/theorems/5a77e3c2-780c-49ca-98b6-f25e1ed03830
-- title:
--   P2 M PI Qn Herm Haar Gen mk  zero 2a7bf532d2bf: P2 M PI Qn Herm Haar Gen mk  zero 2a7bf532d2bf
-- statement:
--   The P2 M PI Qn Herm Haar Gen mk  zero 2a7bf532d2bf construction uses the P2 M PI Qn Herm Haar Gen mk  zero 2a7bf532d2bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L235-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L235-L237

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

theorem P2M_PI_QnHermHaar_Gen_mk__zero_2a7bf532d2bf : mk' hI (0 : β → ℂ) = 0 := by sorry

alias «PI».«QnHermHaar».«Gen».«mk'_zero» := P2M_PI_QnHermHaar_Gen_mk__zero_2a7bf532d2bf
