-- Prove2me | Theorems.Thm_PI_TailWork_tail_odd
-- name    : PI.TailWork.tail_odd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:55.445943+00:00
-- url     : https://prove2.me/theorems/f7f82903-39f1-4acf-a3af-c00e48751606
-- title:
--   Tail Work: tail odd
-- statement:
--   The Tail Work construction uses the tail odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L166-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L166-L219

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset

theorem PI.TailWork.tail_odd (k : ℕ) (hk : 3 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := by sorry
