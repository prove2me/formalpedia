-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_tau_star
-- name    : SPPRevenue.SingleUnit.tau_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:06.469106+00:00
-- url     : https://prove2.me/theorems/4d83303b-cfff-4414-8587-142c7eceea78
-- title:
--   §4.1, p. 15, Solving Problem (FR) — the root τ⋆ > 1 of (1 − e^{−1}) + ∫_1^{τ⋆}(1 − e^{−1/τ})dτ = 1 is unique, τ⋆ = 1.696
-- statement:
--   There is exactly one $T > 1$ with
--   $$(1 - e^{-1}) + \int_1^{T} \big(1 - e^{-1/\tau}\big)\,d\tau = 1,$$
--   and this $T$, the paper's $\tau^\star$, satisfies $1.6955 \le \tau^\star \le 1.6965$.
--
--   The threshold $\tau^\star$ is where the optimal solution of the factor-revealing program switches from $\min(1, 1/\tau)$ to $0$.
--
--   **Formalization Note** The paper reports $\tau^\star = 1.696$ from a numerical solution; the true root is $1.69572\ldots$, so the printed value is a rounding, stated here as the interval $[1.6955, 1.6965]$ of numbers that round to $1.696$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 15, §4.1, Solving Problem (FR)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem tau_star :
    (∃! T : ℝ, 1 < T ∧ frRootEq T) ∧
      ∀ T : ℝ, 1 < T → frRootEq T → 16955 / 10000 ≤ T ∧ T ≤ 16965 / 10000 := by sorry

end SPPRevenue.SingleUnit
