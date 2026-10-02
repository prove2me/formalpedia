-- Prove2me | Theorems.Thm_SennottDP_Discounted_supersolution_ge_stationary_cost
-- name    : SennottDP.Discounted.supersolution_ge_stationary_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:00:02.088674+00:00
-- url     : https://prove2.me/theorems/94cc13fb-9c9d-4790-a3f5-98d34e711307
-- title:
--   Proposition 4.1.2 — a supersolution for a stationary policy dominates its discounted cost
-- statement:
--   Let $\Delta$ be a Markov decision chain, $\alpha \in (0,1)$, $W : S \to [0,\infty]$ a nonnegative function, and $e$ a stationary policy such that
--   $$W(i) \ge C(i,e) + \alpha \sum_j P_{ij}(e) W(j), \qquad i \in S. \tag{4.2}$$
--   Then
--   $$W(i) \ge v_{e,\alpha,n}(i) + \alpha^n E_e[W(X_n) \mid X_0 = i], \qquad i \in S,\ n \ge 1, \tag{4.3}$$
--   and $W \ge V_{e,\alpha}$.
--
--   Here $C(i,e) = C(i,e(i))$ and $P_{ij}(e) = P_{ij}(e(i))$. This comparison principle is the basic tool for bounding the discounted cost of a stationary policy by a supersolution.
--
--   **Formalization Note** $W$ may take the value $+\infty$ (Remark 2.4.2 of the book).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 61, Proposition 4.1.2, (4.2)–(4.3)

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Proposition 4.1.2, p. 61: let `W : S → [0, ∞]` and let `e` be a stationary
policy with `W(i) ≥ C(i,e) + α ∑_j P_{ij}(e) W(j)` for all `i` (4.2). Then
`W(i) ≥ v_{e,α,n}(i) + α^n E_e[W(X_n) | X_0 = i]` for all `i` and `n ≥ 1` (4.3), and
`W ≥ V_{e,α}`. -/
theorem supersolution_ge_stationary_cost {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (W : S → ℝ≥0∞) (e : StationaryPolicy M)
    (hW : ∀ i, bellmanQ M α W i (e.1 i) ≤ W i) :
    (∀ i : S, ∀ n : ℕ, 1 ≤ n →
        finiteHorizonCost M e.toPolicy α n i + (α : ℝ≥0∞) ^ n * expState M e.toPolicy i n W
          ≤ W i) ∧
      ∀ i : S, discountedCost M e.toPolicy α i ≤ W i := by sorry

end SennottDP.Discounted
