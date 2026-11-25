-- Prove2me | Theorems.Thm_PI_VolStabW_unimod_holds
-- name    : PI.VolStabW.unimod_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:55:41.44616+00:00
-- url     : https://prove2.me/theorems/96535d46-cd96-4886-8890-7c60af612074
-- title:
--   Vol Stab W: unimod holds
-- statement:
--   The Vol Stab W construction uses the unimod holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/Unimod.lean#L224-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/Unimod.lean#L224-L231

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem PI.VolStabW.unimod_holds : Unimod := by sorry
