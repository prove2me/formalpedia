-- Prove2me | Theorems.Thm_PI_CntNotIntW_trace_of_ker
-- name    : PI.CntNotIntW.trace_of_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:04.196416+00:00
-- url     : https://prove2.me/theorems/cb7a99b1-d607-4db5-bd7a-f8d68cea36f3
-- title:
--   Cnt Not Int W: trace of ker
-- statement:
--   The Cnt Not Int W construction uses the trace of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/TraceOfKer.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/TraceOfKer.lean#L9-L26

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

theorem PI.CntNotIntW.trace_of_ker {Q A B : Type*} [Field Q] [CommRing A] [Algebra Q A] [FiniteDimensional Q A]
    [Field B] [Algebra Q B] [FiniteDimensional Q B] (π : A →ₐ[Q] B) (hπ : Function.Surjective π)
    (a : A) (ha : ∀ x, π x = 0 → a * x = 0) : Algebra.trace Q A a = Algebra.trace Q B (π a) := by sorry
