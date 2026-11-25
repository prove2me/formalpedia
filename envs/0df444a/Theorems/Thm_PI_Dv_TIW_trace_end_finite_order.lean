-- Prove2me | Theorems.Thm_PI_Dv_TIW_trace_end_finite_order
-- name    : PI.Dv.TIW.trace_end_finite_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:08.514613+00:00
-- url     : https://prove2.me/theorems/e2636865-3a22-4664-9f7a-bc1173aff7e8
-- title:
--   TIW: trace end finite order
-- statement:
--   The TIW construction uses the trace end finite order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/GrpNorm.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/GrpNorm.lean#L47-L63

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

theorem PI.Dv.TIW.trace_end_finite_order {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ Module.finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by sorry
