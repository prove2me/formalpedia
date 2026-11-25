-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NC_ncoordAll_of
-- name    : PI.LevelKSplit.W.NC.ncoordAll_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:07.792601+00:00
-- url     : https://prove2.me/theorems/630cd6ba-fbe7-503e-adf5-cbc88e31ad0c
-- title:
--   NC: ncoord All of
-- statement:
--   The NC construction uses the ncoord All of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean#L75-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

theorem PI.LevelKSplit.W.NC.ncoordAll_of (hH : HeisPAll) (hL : LevPAll) : NCoordAll := by sorry
