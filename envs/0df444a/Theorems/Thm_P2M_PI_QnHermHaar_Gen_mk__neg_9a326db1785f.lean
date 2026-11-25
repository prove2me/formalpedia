-- Prove2me | Theorems.Thm_P2M_PI_QnHermHaar_Gen_mk__neg_9a326db1785f
-- name    : P2M_PI_QnHermHaar_Gen_mk__neg_9a326db1785f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:57:04.998942+00:00
-- url     : https://prove2.me/theorems/9fb95a77-10bd-41cc-8587-86154aa053ca
-- title:
--   P2 M PI Qn Herm Haar Gen mk  neg 9a326db1785f: P2 M PI Qn Herm Haar Gen mk  neg 9a326db1785f
-- statement:
--   The P2 M PI Qn Herm Haar Gen mk  neg 9a326db1785f construction uses the P2 M PI Qn Herm Haar Gen mk  neg 9a326db1785f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L227-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L227-L229

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

theorem P2M_PI_QnHermHaar_Gen_mk__neg_9a326db1785f {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI (-f) = -mk' hI f := by sorry

alias «PI».«QnHermHaar».«Gen».«mk'_neg» := P2M_PI_QnHermHaar_Gen_mk__neg_9a326db1785f
