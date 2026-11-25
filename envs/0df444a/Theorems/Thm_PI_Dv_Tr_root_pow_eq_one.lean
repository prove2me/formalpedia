-- Prove2me | Theorems.Thm_PI_Dv_Tr_root_pow_eq_one
-- name    : PI.Dv.Tr.root_pow_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:48.596652+00:00
-- url     : https://prove2.me/theorems/11883b3c-afca-5819-a3f8-c38096af732a
-- title:
--   Tr: root pow eq one
-- statement:
--   The Tr construction uses the root pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/TraceFiniteOrder.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/TraceFiniteOrder.lean#L9-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Module

theorem PI.Dv.Tr.root_pow_eq_one {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (m : ℕ) (hB : B ^ m = 1) (μ : ℂ)
    (hμ : μ ∈ B.charpoly.roots) : μ ^ m = 1 := by sorry
