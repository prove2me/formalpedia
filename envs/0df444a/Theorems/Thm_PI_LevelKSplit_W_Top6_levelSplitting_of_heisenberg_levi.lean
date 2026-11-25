-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Top6_levelSplitting_of_heisenberg_levi
-- name    : PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:03.486087+00:00
-- url     : https://prove2.me/theorems/68acdf29-5fe8-49e7-9202-03309890abb1
-- title:
--   Top6: level Splitting of heisenberg levi
-- statement:
--   The Top6 construction uses the level Splitting of heisenberg levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfHL.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfHL.lean#L9-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ModulusAllExtensions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfHL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Top6

theorem PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi (hH : PI.LevelKSplit.W.NC.HeisPAll) (hL : PI.LevelKSplit.W.NC.LevPAll) :
    PI.LevelKSplit.LevelSAll := by sorry
