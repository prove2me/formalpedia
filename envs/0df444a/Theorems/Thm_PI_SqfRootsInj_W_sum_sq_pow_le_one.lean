-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_sum_sq_pow_le_one
-- name    : PI.SqfRootsInj.W.sum_sq_pow_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:33.881023+00:00
-- url     : https://prove2.me/theorems/63431688-41f2-5fd7-8a19-321f6bbb38be
-- title:
--   W: sum sq pow le one
-- statement:
--   The W construction uses the sum sq pow le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L37-L47

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

theorem PI.SqfRootsInj.W.sum_sq_pow_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) (n : ℕ) :
    ∑ e ∈ Finset.Icc 1 n, (e : ℝ) ^ 2 * t ^ e ≤ 2 * t := by sorry
