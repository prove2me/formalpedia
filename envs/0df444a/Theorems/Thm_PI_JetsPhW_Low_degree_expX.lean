-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_degree_expX
-- name    : PI.JetsPhW.Low.degree_expX
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:52.165615+00:00
-- url     : https://prove2.me/theorems/6f00c99f-2583-4177-b817-69f82f37017f
-- title:
--   Low: degree exp X
-- statement:
--   The Low construction uses the degree exp X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L73-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]

theorem PI.JetsPhW.Low.degree_expX : Finsupp.degree E0 = 1 := by sorry
