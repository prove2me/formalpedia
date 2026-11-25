-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_MeasAll_maximal_compact_measurable
-- name    : PI.LevelKSplit.W.MeasAll.maximal_compact_measurable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:34:48.989204+00:00
-- url     : https://prove2.me/theorems/9cf3ae62-1c67-45a7-9955-5309775bcf4b
-- title:
--   Meas All: maximal compact measurable
-- statement:
--   The Meas All construction uses the maximal compact measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasAll.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasAll.lean#L8-L10

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

theorem PI.LevelKSplit.W.MeasAll.maximal_compact_measurable : PI.LevelKSplit.W.MeasKfAll := by sorry
