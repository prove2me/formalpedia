-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_pp_lte
-- name    : PI.SqfRootShift.W.pp_lte
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:29.541353+00:00
-- url     : https://prove2.me/theorems/61b6e8bb-069d-5145-97e4-3a3cd9989728
-- title:
--   W: pp lte
-- statement:
--   The W construction uses the pp lte property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L145-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L145-L153

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

theorem PI.SqfRootShift.W.pp_lte {p g k : ℕ} (hp : p.Prime) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hpg : p ∣ g - 1)
    (hk : k ≠ 0) : p ^ (g ^ k - 1).factorization p ≤ k * p ^ (g - 1).factorization p := by sorry
