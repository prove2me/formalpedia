-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_ppSum_le_self
-- name    : PI.SqfRootShift.W.ppSum_le_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:27.391796+00:00
-- url     : https://prove2.me/theorems/96029919-ef6e-523e-a536-124f8f31284e
-- title:
--   W: pp Sum le self
-- statement:
--   The W construction uses the pp Sum le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/SumLeProdOfTwoLe.lean#L40-L44

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

theorem PI.SqfRootShift.W.ppSum_le_self {N : ℕ} (hN : N ≠ 0) : ppSum N ≤ N := by sorry
