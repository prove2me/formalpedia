-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_3_9
-- name    : PolyContract.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:02:17.00238+00:00
-- url     : https://prove2.me/theorems/72f76b00-5c83-46a1-baf6-cd401a1e2402
-- title:
--   Theorem 3.9 — at least $2^n/(1+n(n+1)/2)-1$ breakpoints in $(0,1)$
-- statement:
--   For every $n\ge1$ there is a valid instance $(f,m,\beta)$ with quadratic costs on $n$ elements ($f$ a rank function, $m\ge0$, $\beta>0$) whose best response $x^\star$ has at least
--   $$\frac{2^n}{1+n(n+1)/2}-1$$
--   breakpoints in $(0,1)$.
--
--   So the best-response curve over a polymatroid can have exponentially many affine pieces, and an exact algorithm that enumerates them cannot run in polynomial time in general.
--
--   Differences from the source:
--   - encoding: has at least N breakpoints in (0, 1) → some finite set of breakpoints in (0, 1) has at least N elements; reason: the breakpoint set is finite (Lemma 3.4); the form avoids the cardinality of a possibly infinite set
--   - reading: which is 2^{n−O(log n)} → not stated; reason: an asymptotic rewriting of the explicit bound, implied by it by arithmetic alone; it says nothing further about the instance
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 3.9, p.9 (PDF p.10); proof App. B.5, p.27

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem 3.9** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.9; proof App. B.5, p.27): for every `n ≥ 1` there is an instance on `n` elements
whose best response has at least `2^n/(1 + n(n + 1)/2) − 1` breakpoints in `(0, 1)`.

**Formalization Note** An instance is a valid quadratic-cost instance (rank function, `m ≥ 0`,
`β > 0`) on `Fin n`. "At least `N` breakpoints" is: some finite set of breakpoints in `(0, 1)` has
at least `N` elements. -/
theorem theorem_3_9 (n : ℕ) (hn : 1 ≤ n) :
    ∃ I : QuadInstance (Fin n), I.Valid ∧
      ∃ B : Finset ℝ, (∀ b ∈ B, b ∈ Set.Ioo (0 : ℝ) 1 ∧ I.IsBreakpoint b) ∧
        (2 : ℝ) ^ n / (1 + (n : ℝ) * (n + 1) / 2) - 1 ≤ B.card := by sorry

end PolyContract.Supplement
