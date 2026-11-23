-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Meas_countable_nf
-- name    : PI.LevelKSplit.W.Meas.countable_nf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:03.427825+00:00
-- url     : https://prove2.me/theorems/c76d15fe-2891-4224-95e7-9187199b5c14
-- title:
--   Meas: countable nf
-- statement:
--   The Meas construction uses the countable nf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/CompVInvMulVec.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/CompVInvMulVec.lean#L14-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CompVInvMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Meas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct

theorem PI.LevelKSplit.W.Meas.countable_nf (K : Type) [Field K] [NumberField K] : Countable K := by sorry
