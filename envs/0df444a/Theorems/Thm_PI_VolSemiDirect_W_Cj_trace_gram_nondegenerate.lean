-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_trace_gram_nondegenerate
-- name    : PI.VolSemiDirect.W.Cj.trace_gram_nondegenerate
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:42.662259+00:00
-- url     : https://prove2.me/theorems/279bac56-a2e8-4a55-946c-6627386a781e
-- title:
--   Cj: trace gram nondegenerate
-- statement:
--   The Cj construction uses the trace gram nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TraceGramNondegenerate.lean#L71-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TraceGramNondegenerate.lean#L71-L98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TraceGramNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

theorem PI.VolSemiDirect.W.Cj.trace_gram_nondegenerate : TraceGramND := by sorry
