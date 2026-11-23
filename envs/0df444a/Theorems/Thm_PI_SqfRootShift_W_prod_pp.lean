-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_prod_pp
-- name    : PI.SqfRootShift.W.prod_pp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:20.782047+00:00
-- url     : https://prove2.me/theorems/b499bf31-1d87-4436-b1de-cc28749778c4
-- title:
--   W: prod pp
-- statement:
--   The W construction uses the prod pp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L36-L38

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

theorem PI.SqfRootShift.W.prod_pp {N : ℕ} (hN : N ≠ 0) : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by sorry
