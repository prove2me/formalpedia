-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_levelSAll_of
-- name    : PI.LevelKSplit.W.levelSAll_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:09.648678+00:00
-- url     : https://prove2.me/theorems/78759801-c224-55e4-bf69-d7a0606bbe1b
-- title:
--   W: level SAll of
-- statement:
--   The W construction uses the level SAll of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOf.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOf.lean#L130-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelKSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

theorem PI.LevelKSplit.W.levelSAll_of (h1 : ExistSAll) (h2 : MeasKfAll) (h3 : SplitKAll) : LevelSAll := by sorry
