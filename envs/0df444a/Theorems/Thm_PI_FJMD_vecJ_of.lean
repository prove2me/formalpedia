-- Prove2me | Theorems.Thm_PI_FJMD_vecJ_of
-- name    : PI.FJMD.vecJ_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:08.223246+00:00
-- url     : https://prove2.me/theorems/0009c2de-b23c-5737-8b1a-77579809641a
-- title:
--   FJMD: vec J of
-- statement:
--   The FJMD construction uses the vec J of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L194-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L194-L238

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM

theorem PI.FJMD.vecJ_of (hF : FormJ) : VecJ := by sorry
