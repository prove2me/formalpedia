-- Prove2me | Theorems.Thm_PI_Dv_TIW_trace_finite_order
-- name    : PI.Dv.TIW.trace_finite_order
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:37.046616+00:00
-- url     : https://prove2.me/theorems/77810aba-1f92-401a-9366-f7f7d4a11f00
-- title:
--   TIW: trace finite order
-- statement:
--   The TIW construction uses the trace finite order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/GrpNorm.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/GrpNorm.lean#L31-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Matrix

theorem PI.Dv.TIW.trace_finite_order {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hm : 0 < m)
    (hM : M ^ m = 1) : ‖M.trace‖ ≤ Fintype.card d ∧ IsIntegral ℤ M.trace := by sorry
