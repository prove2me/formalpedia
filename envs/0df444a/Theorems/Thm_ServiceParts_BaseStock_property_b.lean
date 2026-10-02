-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_property_b
-- name    : ServiceParts.BaseStock.property_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:30:24.150428+00:00
-- url     : https://prove2.me/theorems/a107cddb-809e-48ab-ac85-396ad574e544
-- title:
--   Property (b) — the derivative of $f_n$ on either side of the order-up-to level
-- statement:
--   In the model of Section 2.1 with lead time one period, let $n \ge 2$ and suppose the order-up-to rule $u(y) = \max\{0, s-y\}$ with a real level $s$ is optimal in the $n$-period problem at every inventory position. Then $f_n$ is differentiable at every $y$, with
--   $$
--   f_n'(y) = \begin{cases} -c + L'(y), & y < s,\\[1mm] L'(y) + \alpha\displaystyle\int_0^\infty f_{n-1}'(y-x)\,g(x)\,dx, & y \ge s. \end{cases}
--   $$
--
--   Below the level the optimal order raises the position to $s$, so only the purchase and the current period's cost vary with $y$; above it nothing is ordered.
--
--   **Formalization Note** The book's $s_n^*$ is "the unique solution of (2.6)"; here $s$ is any real level at which the order-up-to rule is optimal, which is how the book uses $s_n^*$. The conclusion is a `HasDerivAt` statement, so differentiability of $f_n$ is asserted, not presupposed.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 19, Section 2.1, proof of Theorem 2 (property (b)); re-established as eq. (2.10), p. 20

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Property (b) in the proof of Theorem 2, p. 19 (re-established as (2.10), p. 20): if the
order-up-to rule with level s is optimal in the n-period problem (n ≥ 2), then fₙ is
differentiable at every y, with f′ₙ(y) = −c + L′(y) for y < s and
f′ₙ(y) = L′(y) + α ∫₀^∞ f′ₙ₋₁(y − x) g(x) dx for y ≥ s. -/
theorem property_b (M : Model) (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (y : ℝ) :
    HasDerivAt (M.f n)
      (if y < s then -M.c + deriv M.L y
       else deriv M.L y + M.α * ∫ x in Ioi (0 : ℝ), deriv (M.f (n - 1)) (y - x) * M.g x) y := by sorry

end ServiceParts.BaseStock
