-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NC_conjNHAll_of
-- name    : PI.LevelKSplit.W.NC.conjNHAll_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:18.74796+00:00
-- url     : https://prove2.me/theorems/76052248-2468-433d-ac2b-2a812c85e0d9
-- title:
--   NC: conj NHAll of
-- statement:
--   The NC construction uses the conj NHAll of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCDefs.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCDefs.lean#L95-L97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_FiniteAdelesSecondCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
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
open PI.LevelKSplit.W.ExS PI.LevelKSplit.W.CD
open scoped TensorProduct

theorem PI.LevelKSplit.W.NC.conjNHAll_of (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) : ConjNHAll := by sorry
