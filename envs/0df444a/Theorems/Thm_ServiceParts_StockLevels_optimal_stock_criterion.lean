-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_optimal_stock_criterion
-- name    : ServiceParts.StockLevels.optimal_stock_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:28:22.109803+00:00
-- url     : https://prove2.me/theorems/1ce6fab1-af89-473e-a4a9-20cca7b36de5
-- title:
--   Section 3.4.2, p. 61 — the smallest s with Σ_{x≤s} p(x|µ) ≥ 1/(1+θc) minimizes f(s) = (1+θc)B(s) + θcs
-- statement:
--   Let an item have compound Poisson demand with steady-state probabilities $p(x \mid \mu)$ and expected backorders $B(s)$, unit cost $c > 0$, and let $\theta > 0$ be a Lagrange multiplier. Put
--   $$f(s) = (1 + \theta c)\,B(s) + \theta c\,s, \qquad s = 0, 1, 2, \dots$$
--   Then:
--
--   1. $f$ is discretely convex: $\Delta^2 f(s) \ge 0$ for all $s$;
--   2. $\Delta f(s) = -(1 + \theta c)\big(1 - \sum_{x \le s} p(x \mid \mu)\big) + \theta c$;
--   3. $\Delta f(s) \ge 0$ if and only if
--   $$\sum_{x \le s} p(x \mid \mu) \ge \frac{1}{1 + \theta c};$$
--   4. some $s$ satisfies this inequality;
--   5. the smallest such $s$, call it $s^*$, is an optimal stock level: $f(s^*) \le f(s)$ for every $s \ge 0$, and $f(s^*) < f(s)$ for every $s < s^*$.
--
--   This solves the single-item subproblem of the Lagrangian relaxation of Problem 4, which separates by item type.
--
--   **Formalization Note** The book allows $\theta \ge 0$ in (3.38). Here $\theta > 0$ and $c > 0$ are assumed: at $\theta = 0$ the threshold is $1$, which the distribution function of a compound Poisson law never reaches, and $f = B$ has no minimizer. Optimality is against every nonnegative integer $s$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 61, Section 3.4.2 (f(s), Δf(s), and the optimal stock level s*)

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem optimal_stock_criterion (d : CompoundPoissonDemand) (c θ : ℝ) (hc : 0 < c)
    (hθ : 0 < θ) :
    (∀ s, 0 ≤ fdiff2 (relaxedCost d c θ) s) ∧
    (∀ s, fdiff (relaxedCost d c θ) s = -(1 + θ * c) * (1 - d.readyRate s) + θ * c) ∧
    (∀ s, 0 ≤ fdiff (relaxedCost d c θ) s ↔ s ∈ stockSet d c θ) ∧
    (stockSet d c θ).Nonempty ∧
    ∀ sStar : ℕ, IsLeast (stockSet d c θ) sStar →
      (∀ s, relaxedCost d c θ sStar ≤ relaxedCost d c θ s) ∧
      (∀ s, s < sStar → relaxedCost d c θ sStar < relaxedCost d c θ s) := by sorry

end ServiceParts.StockLevels
