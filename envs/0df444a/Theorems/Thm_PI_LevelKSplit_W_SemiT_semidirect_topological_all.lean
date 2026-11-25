-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiT_semidirect_topological_all
-- name    : PI.LevelKSplit.W.SemiT.semidirect_topological_all
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:58.688538+00:00
-- url     : https://prove2.me/theorems/c5877e80-e195-4533-910e-cb724b7bdf78
-- title:
--   Semi T: semidirect topological all
-- statement:
--   The Semi T construction uses the semidirect topological all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiTop.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiTop.lean#L108-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem PI.LevelKSplit.W.SemiT.semidirect_topological_all : PI.LevelKSplit.W.ExS.SemiNHSAll := by sorry
