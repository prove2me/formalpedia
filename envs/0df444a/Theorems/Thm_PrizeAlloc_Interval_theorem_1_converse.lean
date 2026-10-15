-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_theorem_1_converse
-- name    : PrizeAlloc.Interval.theorem_1_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:42.715648+00:00
-- url     : https://prove2.me/theorems/7807a142-a72c-410a-8893-fb6d9d1ba14b
-- title:
--   Theorem 1, "if" direction (p. 28) — every interval rule satisfies order preservation, endowment monotonicity and consistency
-- statement:
--   Let $\varphi$ be a prize allocation rule that is an interval rule. Then $\varphi$ satisfies
--
--   1. order preservation,
--   2. endowment monotonicity, and
--   3. consistency.
--
--   This is the direction of Theorem 1 that the paper calls readily checked; together with the converse direction it gives the characterization.
--
--   **Formalization Note** No assumption on the size of $U$ is needed for this direction.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 28, proof of Theorem 1, first sentence

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem theorem_1_converse {U : Type*} [DecidableEq U] (φ : List U → ℝ → U → ℝ)
    (hφ : IsPrizeRule φ) (hInt : IsIntervalRule φ) :
    OrderPreserving φ ∧ EndowmentMonotone φ ∧ Consistent φ := by sorry

end PrizeAlloc.Interval
