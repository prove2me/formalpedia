-- Prove2me | Theorems.Thm_PI_GGConvScalarW_sum_boole_uni
-- name    : PI.GGConvScalarW.sum_boole_uni
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:54.106001+00:00
-- url     : https://prove2.me/theorems/ce7b6869-a98f-46fb-988a-aed8e83ba769
-- title:
--   GGConv Scalar W: sum boole uni
-- statement:
--   The GGConv Scalar W construction uses the sum boole uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/AveragingOperatorIdempotent.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/AveragingOperatorIdempotent.lean#L41-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PI.GGConvScalarW.sum_boole_uni : (∑ x : GL (Fin k) F, if IsUni k x then (1 : ℂ) else 0) = (cardU F k : ℂ) := by sorry
