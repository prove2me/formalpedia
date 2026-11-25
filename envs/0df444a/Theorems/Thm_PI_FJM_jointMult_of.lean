-- Prove2me | Theorems.Thm_PI_FJM_jointMult_of
-- name    : PI.FJM.jointMult_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:54.121611+00:00
-- url     : https://prove2.me/theorems/13cc5d36-0657-4f49-aab7-1296623bb531
-- title:
--   FJM: joint Mult of
-- statement:
--   The FJM construction uses the joint Mult of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/JointMultOfSteps.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/JointMultOfSteps.lean#L42-L53

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
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
open PI PI.FJM

theorem PI.FJM.jointMult_of (he : Exist) (hs : ShapeOf) (hr : RankLe) : PI.FockDegreeTwoParts.JointMult := by sorry
