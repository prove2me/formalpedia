-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_deriv_bounds
-- name    : ServiceParts.BaseStock.deriv_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T21:28:12.467031+00:00
-- url     : https://prove2.me/theorems/61915fdc-357d-440b-a313-876424bc52d7
-- title:
--   Bounds $-(c+b) \le f_n' \le h/(1-\alpha)$ on the value-function slopes
-- statement:
--   In the model of Section 2.1 with lead time one period, for every horizon $n \ge 1$ the value function $f_n$ is differentiable on $\mathbb R$ and its derivative satisfies
--   $$
--   -(c+b) \;\le\; f_n'(y) \;\le\; \frac{h}{1-\alpha} \qquad \text{for all } y \in \mathbb R .
--   $$
--
--   These uniform bounds justify the dominated-convergence step that yields the limits of $F_n(w)$ as $w \to \pm\infty$, and hence the existence of the next order-up-to level.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 20, Section 2.1, proof of Theorem 2

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 20: fₙ is differentiable and "f′ₙ(·) is bounded above and below by
h/(1 − α) and −(c + b), respectively", for every horizon n ≥ 1. -/
theorem deriv_bounds (M : Model) (n : ℕ) (hn : 1 ≤ n) :
    Differentiable ℝ (M.f n) ∧
      ∀ y : ℝ, -(M.c + M.b) ≤ deriv (M.f n) y ∧ deriv (M.f n) y ≤ M.h / (1 - M.α) := by sorry

end ServiceParts.BaseStock
