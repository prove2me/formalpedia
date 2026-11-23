-- Prove2me | Theorems.Thm_PI_CntNotIntW_trace_one_tmul
-- name    : PI.CntNotIntW.trace_one_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:07.809398+00:00
-- url     : https://prove2.me/theorems/eaca901d-8685-4916-b576-b4e7cdcc15d8
-- title:
--   Cnt Not Int W: trace one tmul
-- statement:
--   The Cnt Not Int W construction uses the trace one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/TraceOfKer.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/TraceOfKer.lean#L28-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_TraceOfKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct

theorem PI.CntNotIntW.trace_one_tmul {Q K : Type*} [Field Q] [Algebra ℚ Q] [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (y : K) : Algebra.trace Q (Q ⊗[ℚ] K) (1 ⊗ₜ y) = algebraMap ℚ Q (Algebra.trace ℚ K y) := by sorry
