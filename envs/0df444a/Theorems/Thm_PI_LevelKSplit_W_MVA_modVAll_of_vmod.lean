-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_MVA_modVAll_of_vmod
-- name    : PI.LevelKSplit.W.MVA.modVAll_of_vmod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:10.195131+00:00
-- url     : https://prove2.me/theorems/4e5ddc11-3c26-5542-9e56-446402d33031
-- title:
--   MVA: mod VAll of vmod
-- statement:
--   The MVA construction uses the mod VAll of vmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ModulusAllExtensions.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ModulusAllExtensions.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_OrthogonalInvarianceOfStableRankOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ModulusAllExtensions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem PI.LevelKSplit.W.MVA.modVAll_of_vmod (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by sorry
