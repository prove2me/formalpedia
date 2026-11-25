-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_harm_tail
-- name    : PI.SqfRootShift.W.harm_tail
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:09.808963+00:00
-- url     : https://prove2.me/theorems/bde1700f-a77c-4fe6-95cf-c23333d1d94f
-- title:
--   W: harm tail
-- statement:
--   The W construction uses the harm tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/ArithP.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/ArithP.lean#L24-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_ArithP
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

theorem PI.SqfRootShift.W.harm_tail (r : ℕ) (hr : 1 ≤ r) : ∑ k ∈ Finset.Ioc 1 r, ((k : ℝ))⁻¹ ≤ Real.log r := by sorry
