-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_corollary_prop_5
-- name    : Sennott1989.AvgCost.corollary_prop_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:47.909317+00:00
-- url     : https://prove2.me/theorems/aa43067b-202e-4280-977e-12752be78107
-- title:
--   Corollary (to Proposition 5), p. 630 — an irreducible chain with a drift test function and costs bounded away from 0 gives Assumptions 1 and 3
-- statement:
--   Consider a Markov decision chain on $0,1,2,\dots$ with finite action sets and nonnegative costs. Assume there is a stationary policy $f$ inducing an irreducible Markov chain, a nonnegative function $r$ and a nonnegative integer $N$ such that
--   $$\sum_jP_{ij}(f)r(j)<\infty\quad(0\le i\le N),\qquad \sum_jP_{ij}(f)r(j)-r(i)\le-C(i,f)\quad(i>N),$$
--   and that the costs $C(i,f)$, $i>N$, are positive and bounded away from $0$. Then Assumptions 1 and 3 hold.
--
--   This is the form in which the paper applies its results: one test function for one policy.
--
--   **Formalization Note** Only irreducibility is assumed; ergodicity of the chain is a consequence (Pakes 1969), not a hypothesis. "Bounded away from 0" is $\exists\varepsilon>0$ with $C(i,f)\ge\varepsilon$ for all $i>N$. The drift inequality is written $\sum_jP_{ij}(f)r(j)+C(i,f)\le r(i)$ in $[0,\infty]$ ($r$ is finite).
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Corollary (to Proposition 5), p. 630

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §2, Corollary (to Proposition 5), p. 630. Assume that there exists a
stationary policy `f` inducing an irreducible Markov chain with the following property: there
exist a nonnegative function `r` and a nonnegative integer `N` such that
`∑_j P_{ij}(f) r(j) < ∞` for `0 ≤ i ≤ N`, and `∑_j P_{ij}(f) r(j) − r(i) ≤ −C(i, f)` for
`i > N`. If, finally, the costs `C(i, f)`, `i > N`, are positive and bounded away from `0`, then
Assumptions 1 and 3 hold.

**Formalization Note** Only irreducibility is assumed (ergodicity is a consequence). `r` is
finite and nonnegative, so the drift condition is written
`∑_j P_{ij}(f) r(j) + C(i, f) ≤ r(i)` in `[0, ∞]`. "Positive and bounded away from 0" is
`∃ ε > 0, ∀ i > N, ε ≤ C(i, f)`. -/
theorem corollary_prop_5 {Act : Type} (M : MDC ℕ Act) (f : StationaryPolicy M)
    (hirr : SennottDP.MarkovCost.Irreducible (inducedChain M f))
    (r : ℕ → ℝ≥0) (N : ℕ)
    (hfin : ∀ i, i ≤ N → ∑' j, M.P i (f.1 i) j * (r j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i, N < i →
      ∑' j, M.P i (f.1 i) j * (r j : ℝ≥0∞) + (M.C i (f.1 i) : ℝ≥0∞) ≤ (r i : ℝ≥0∞))
    (hpos : ∃ ε : ℝ≥0, 0 < ε ∧ ∀ i, N < i → ε ≤ M.C i (f.1 i)) :
    Assumption1 M ∧ ∃ Mb : ℕ → ℝ, Assumption3 M Mb := by sorry

end Sennott1989.AvgCost
