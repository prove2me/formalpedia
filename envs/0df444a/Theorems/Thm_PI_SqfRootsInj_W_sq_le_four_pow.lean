-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_sq_le_four_pow
-- name    : PI.SqfRootsInj.W.sq_le_four_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:05.561975+00:00
-- url     : https://prove2.me/theorems/2c7df2f7-f8a4-4ed2-8308-97359014477d
-- title:
--   W: sq le four pow
-- statement:
--   The W construction uses the sq le four pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L17-L27

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

theorem PI.SqfRootsInj.W.sq_le_four_pow (e : ℕ) (he : 1 ≤ e) : e ^ 2 ≤ 4 ^ (e - 1) := by sorry
