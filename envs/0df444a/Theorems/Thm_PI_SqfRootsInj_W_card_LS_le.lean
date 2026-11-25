-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_card_LS_le
-- name    : PI.SqfRootsInj.W.card_LS_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:58.675889+00:00
-- url     : https://prove2.me/theorems/0fb0008d-5646-4985-ad54-6e78bc948945
-- title:
--   W: card LS le
-- statement:
--   The W construction uses the card LS le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L64-L73

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

theorem PI.SqfRootsInj.W.card_LS_le (g r n : ℕ) (hn : n ≠ 0) :
    ((LS g r n).card : ℝ) ≤ Real.log n / Real.log 2 := by sorry
