-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_f_convex
-- name    : ServiceParts.BaseStock.f_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:27:08.864121+00:00
-- url     : https://prove2.me/theorems/5ff8a0fe-41f2-4b25-867b-c7b9a2dc08eb
-- title:
--   Convexity of the n-period value functions $f_n$
-- statement:
--   In the model of Section 2.1 with lead time one period, for every horizon $n \ge 1$ the value function $f_n$ defined by $f_1 = L$ and
--   $$
--   f_n(y) = \min_{u \ge 0}\Big\{ c\,u + L(y) + \alpha\int_0^\infty f_{n-1}(y+u-x)\,g(x)\,dx \Big\}
--   $$
--   is a convex function of $y \in \mathbb R$.
--
--   This is the convexity part of property (c) in the Karlin–Scarf induction; it makes $F_n$ nondecreasing, which is what turns the first-order condition into an order-up-to rule.
--
--   **Formalization Note** The book's property (c) also claims that $f_n''$ exists everywhere except possibly at $s_n^*$. That clause fails in general (for $y$ below the level, $f_n''$ equals $L''$, which jumps at $y = 0$ when $g(0^+) > 0$, e.g. for exponential demand), so only convexity is stated.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 19, Section 2.1, proof of Theorem 2 (property (c), convexity clause)

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 19: "Recall that fₙ(y) is a convex function." For every horizon n ≥ 1. -/
theorem f_convex (M : Model) (n : ℕ) (hn : 1 ≤ n) : ConvexOn ℝ univ (M.f n) := by sorry

end ServiceParts.BaseStock
