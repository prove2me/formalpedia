-- Prove2me | Theorems.Thm_PI_Dv_Tr_trace_finite_order
-- name    : PI.Dv.Tr.trace_finite_order
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:53.135987+00:00
-- url     : https://prove2.me/theorems/629bc7a2-e90e-4d10-822b-226be0a5864a
-- title:
--   Tr: trace finite order
-- statement:
--   The Tr construction uses the trace finite order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/TraceFiniteOrder.lean#L36-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/TraceFiniteOrder.lean#L36-L67

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
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem PI.Dv.Tr.trace_finite_order (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by sorry
