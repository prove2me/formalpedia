-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_sq_mul_pow_le
-- name    : PI.SqfRootsInj.W.sq_mul_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:40.050812+00:00
-- url     : https://prove2.me/theorems/dde61b62-3cb3-4d06-bd1a-36b46580f116
-- title:
--   W: sq mul pow le
-- statement:
--   The W construction uses the sq mul pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L29-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.sq_mul_pow_le (t : ℝ) (ht0 : 0 ≤ t) (e : ℕ) (he : 1 ≤ e) :
    (e : ℝ) ^ 2 * t ^ e ≤ t * (4 * t) ^ (e - 1) := by sorry
