-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_two_le_pp
-- name    : PI.SqfRootShift.W.two_le_pp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:09.428468+00:00
-- url     : https://prove2.me/theorems/dd8d6336-894f-454d-9d60-ae86895d02ab
-- title:
--   W: two le pp
-- statement:
--   The W construction uses the two le pp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L33-L34

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

theorem PI.SqfRootShift.W.two_le_pp {N p : ℕ} (hp : p ∈ N.primeFactors) : 2 ≤ p ^ N.factorization p := by sorry
