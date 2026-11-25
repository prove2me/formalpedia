-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_MeasAll_levelSAll_of_exist
-- name    : PI.LevelKSplit.W.MeasAll.levelSAll_of_exist
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:34:31.286514+00:00
-- url     : https://prove2.me/theorems/13d47a4d-919d-4347-9553-e5ab33de8784
-- title:
--   Meas All: level SAll of exist
-- statement:
--   The Meas All construction uses the level SAll of exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasAll.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasAll.lean#L12-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasurableSetBorelOfIsClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MeasAll

theorem PI.LevelKSplit.W.MeasAll.levelSAll_of_exist (h1 : PI.LevelKSplit.W.ExistSAll) : PI.LevelKSplit.LevelSAll := by sorry
