-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Meas_measurableSet_borel_of_isClosed
-- name    : PI.LevelKSplit.W.Meas.measurableSet_borel_of_isClosed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:34:12.204045+00:00
-- url     : https://prove2.me/theorems/5b87088e-6fe4-4a23-9c0e-d363d4144b24
-- title:
--   Meas: measurable Set borel of is Closed
-- statement:
--   The Meas construction uses the measurable Set borel of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasurableSetBorelOfIsClosed.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MeasurableSetBorelOfIsClosed.lean#L11-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CompVInvMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasurableSetBorelOfIsClosed
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
open scoped TensorProduct

theorem PI.LevelKSplit.W.Meas.measurableSet_borel_of_isClosed {X : Type} [TopologicalSpace X] {s : Set X}
    (h : IsClosed s) : MeasurableSet[borel X] s := by sorry
