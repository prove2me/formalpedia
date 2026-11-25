-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_sum_sq_pow_le_two
-- name    : PI.SqfRootsInj.W.sum_sq_pow_le_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:22.379792+00:00
-- url     : https://prove2.me/theorems/b4a8500a-8d06-58a3-9da8-0ad6c2b5d100
-- title:
--   W: sum sq pow le two
-- statement:
--   The W construction uses the sum sq pow le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L49-L62

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

theorem PI.SqfRootsInj.W.sum_sq_pow_le_two (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) (n : ℕ) :
    ∑ e ∈ Finset.Icc 2 n, (e : ℝ) ^ 2 * t ^ e ≤ 8 * t ^ 2 := by sorry
