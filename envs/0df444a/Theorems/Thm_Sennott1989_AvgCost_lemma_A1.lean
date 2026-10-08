-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_lemma_A1
-- name    : Sennott1989.AvgCost.lemma_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:30.826982+00:00
-- url     : https://prove2.me/theorems/e826544d-ac2c-49b1-a439-a4978622e80b
-- title:
--   Lemma A1 (p. 632) — a bounded-below supersolution of (A1) bounds g_f above by g; a bounded subsolution bounds it below
-- statement:
--   Let $f$ be a stationary policy, $g$ a real constant, and $h$ a real function on the states.
--
--   1. If $-N\le h(i)$ for every $i$ and
--   $$g+h(i)\ \ge\ C(i,f)+\sum_jP_{ij}(f)h(j),\qquad i\ge0,\tag{A1}$$
--   then $g_f(i)\le g$ for every $i$.
--   2. If the inequality in (A1) is reversed and $h(i)\le N$ for all $i$, then $g_f(i)\ge g$ for every $i$.
--
--   Here $g_f(i)$ is the lim sup average cost of $f$ from $i$. The first statement is the verification step that turns the optimality inequality (5) into an upper bound on average cost.
--
--   **Formalization Note** $g_f(i)\in[0,\infty]$ is compared with $g$ in the extended reals; $g$ may be any real number. The sum $\sum_jP_{ij}(f)h(j)$ is the extended-real positive-part-minus-negative-part sum. Its negative part is finite in the first case, and its positive part is finite in the second.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, Appendix, Lemma A1, (A1), p. 632

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), Appendix, Lemma A1, p. 632. Let `g` be a real constant, `h` a real function,
and `f` a stationary policy.

1. If `−N ≤ h(i)` and `g + h(i) ≥ C(i, f) + ∑_j P_{ij}(f) h(j)` for all `i ≥ 0` (A1), then
   `g_f(i) ≤ g` for every `i`.
2. If the inequality in (A1) is reversed and `h(i) ≤ N` for all `i`, then `g_f(i) ≥ g` for all `i`.

**Formalization Note** `g_f(i)` is the lim sup average cost `SennottDP.SEN.avgCost` in `[0, ∞]`,
compared with the real `g` in `EReal`; `g` may be any real number. The sum `∑_j P_{ij}(f) h(j)` is
the extended-real `SennottDP.SEN.wsum`: its negative part is finite in the first case, and its
positive part is finite in the second. -/
theorem lemma_A1 {Act : Type} (M : MDC ℕ Act) (f : StationaryPolicy M) (g : ℝ) (h : ℕ → ℝ)
    (N : ℝ) :
    ((∀ i, -N ≤ h i) →
      (∀ i, acoiTerm M h i (f.1 i) ≤ ((g + h i : ℝ) : EReal)) →
        ∀ i, (SennottDP.SEN.avgCost M f.toPolicy i : EReal) ≤ (g : EReal)) ∧
      ((∀ i, h i ≤ N) → (∀ i, ((g + h i : ℝ) : EReal) ≤ acoiTerm M h i (f.1 i)) →
        ∀ i, (g : EReal) ≤ (SennottDP.SEN.avgCost M f.toPolicy i : EReal)) := by sorry

end Sennott1989.AvgCost
