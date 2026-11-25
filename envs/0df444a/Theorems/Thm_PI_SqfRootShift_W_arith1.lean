-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_arith1
-- name    : PI.SqfRootShift.W.arith1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:28.208481+00:00
-- url     : https://prove2.me/theorems/6947e75f-3199-4a8b-8bf1-bb5afb1264a9
-- title:
--   W: arith1
-- statement:
--   The W construction uses the arith1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L46-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L46-L108

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
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
open PI PI.SqfRootShift PI.SqfRootShift.W

theorem PI.SqfRootShift.W.arith1 {n q d : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hd : d.Prime) (hqd : q ≠ d)
    (hq16 : 16 ≤ q) (hd16 : 16 ≤ d) (h16 : 16 ∣ n) (hqn : q ∣ n) (hdn : d ∣ n) :
    4 * min q d * ppSum n ≤ n := by sorry
