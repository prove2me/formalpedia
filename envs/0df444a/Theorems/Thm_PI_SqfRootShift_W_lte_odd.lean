-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_lte_odd
-- name    : PI.SqfRootShift.W.lte_odd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:09.170952+00:00
-- url     : https://prove2.me/theorems/dd5bd917-78be-5ac8-8c2e-861a23ecb05b
-- title:
--   W: lte odd
-- statement:
--   The W construction uses the lte odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L134-L143

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

theorem PI.SqfRootShift.W.lte_odd {p g k : ℕ} [Fact p.Prime] (hp : Odd p) (hg : 2 ≤ g) (hpg : p ∣ g - 1)
    (hk : k ≠ 0) : padicValNat p (g ^ k - 1) = padicValNat p (g - 1) + padicValNat p k := by sorry
