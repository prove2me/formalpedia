-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NC_levelSAll_of_parts
-- name    : PI.LevelKSplit.W.NC.levelSAll_of_parts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:47.749077+00:00
-- url     : https://prove2.me/theorems/4a0d4095-f497-5100-97c4-0e41bf07513d
-- title:
--   NC: level SAll of parts
-- statement:
--   The NC construction uses the level SAll of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCDefs.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCDefs.lean#L99-L103

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

theorem PI.LevelKSplit.W.NC.levelSAll_of_parts (hS : SemiNHSAll) (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) :
    PI.LevelKSplit.LevelSAll := by sorry
