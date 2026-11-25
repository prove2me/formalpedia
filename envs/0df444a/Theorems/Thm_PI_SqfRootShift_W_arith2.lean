-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_arith2
-- name    : PI.SqfRootShift.W.arith2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:32.020099+00:00
-- url     : https://prove2.me/theorems/3814e708-9080-5731-b26b-1ada63c35737
-- title:
--   W: arith2
-- statement:
--   The W construction uses the arith2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L155-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L155-L196

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

theorem PI.SqfRootShift.W.arith2 {g k : ℕ} (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hk : k ≠ 0) :
    ppSum (g ^ k - 1) ≤ k * ppSum (g - 1) + (g ^ k - 1) / (g - 1) := by sorry
