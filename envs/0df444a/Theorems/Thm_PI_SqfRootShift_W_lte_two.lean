-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_lte_two
-- name    : PI.SqfRootShift.W.lte_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:16.726933+00:00
-- url     : https://prove2.me/theorems/fb1e7c69-1169-5aa4-832e-9dd637276a49
-- title:
--   W: lte two
-- statement:
--   The W construction uses the lte two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L110-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L110-L132

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

theorem PI.SqfRootShift.W.lte_two {g k : ℕ} (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hk : k ≠ 0) :
    padicValNat 2 (g ^ k - 1) = padicValNat 2 (g - 1) + padicValNat 2 k := by sorry
