-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_optimal_stock_level
-- name    : ServiceParts.Shortfall.optimal_stock_level
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:46:41.617233+00:00
-- url     : https://prove2.me/theorems/83233cc7-6d3c-40ee-80d7-63a747f1e123
-- title:
--   Section 8.3.1 — the optimal stock level is the smallest s with Σ_{j>s} p_i(j) = η_i^{s+1} ≤ h_i/(h_i + b)
-- statement:
--   In the repair system of Section 8.3.1, let $0 < \lambda_i \le \lambda < \mu$, $\eta_i = \lambda_i/(\mu - \lambda + \lambda_i)$ and $p_i(j) = (1 - \eta_i)\eta_i^j$. Let $h_i > 0$ be the holding cost rate and $b > 0$ the backorder cost rate, and for $s = 0, 1, 2, \dots$ let
--   $$C_i(s) = h_i \sum_{j=0}^{s} (s - j)\,p_i(j) + b \sum_{j \ge s} (j - s)\,p_i(j).$$
--   Then
--
--   1. for every $s$, $\displaystyle\sum_{j = s+1}^{\infty} p_i(j) = \eta_i^{\,s+1}$;
--   2. a nonnegative integer $s$ is the smallest minimiser of $C_i$ over $\{0, 1, 2, \dots\}$ if and only if it is the smallest nonnegative integer with
--   $$\sum_{j = s+1}^{\infty} p_i(j) \le \frac{h_i}{h_i + b}.$$
--
--   This is the newsvendor rule for the stock level of item $i$ in the capacity-limited repair system; with item 1 it becomes the explicit rule $\eta_i^{s+1} \le h_i/(h_i + b)$.
--
--   **Formalization Note** "The optimal $s_i$" is read as the smallest minimiser (the cost can have two adjacent minimisers when $\eta_i^{s+1} = h_i/(h_i + b)$ exactly). The page's backorder cost is $b$ without index, as printed.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 205, Section 8.3.1 (newsvendor stock level)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_RepairStock

open MeasureTheory

namespace ServiceParts.Shortfall

/-- Section 8.3.1, p. 205. With `p_i(j) = (1 − η_i)η_i^j`, `η_i = λ_i/(µ − λ + λ_i)`, holding cost
rate `h_i > 0` and backorder cost rate `b > 0`:
1. `∑_{j ≥ s+1} p_i(j) = η_i^{s+1}` for every `s`;
2. a nonnegative integer `s` is the smallest minimiser of the cost
   `h_i ∑_{j=0}^{s}(s − j)p_i(j) + b ∑_{j ≥ s}(j − s)p_i(j)` over `s = 0, 1, …` exactly when it is
   the smallest nonnegative integer with `∑_{j ≥ s+1} p_i(j) ≤ h_i/(h_i + b)`. -/
theorem optimal_stock_level (lamI lam mu h b : ℝ) (hlamI : 0 < lamI) (hlamI_le : lamI ≤ lam)
    (hstable : lam < mu) (hh : 0 < h) (hb : 0 < b) :
    (∀ s : ℕ, (∑' j : ℕ, if s + 1 ≤ j then geomPMF (repairEta lamI lam mu) j else 0) =
        repairEta lamI lam mu ^ (s + 1)) ∧
    ∀ s : ℕ,
      ((∀ t : ℕ, stockCost h b (repairEta lamI lam mu) s ≤
            stockCost h b (repairEta lamI lam mu) t) ∧
        ∀ t : ℕ, stockCost h b (repairEta lamI lam mu) t ≤
            stockCost h b (repairEta lamI lam mu) s → s ≤ t) ↔
      ((∑' j : ℕ, if s + 1 ≤ j then geomPMF (repairEta lamI lam mu) j else 0) ≤ h / (h + b) ∧
        ∀ t : ℕ, t < s →
          h / (h + b) < ∑' j : ℕ, if t + 1 ≤ j then geomPMF (repairEta lamI lam mu) j else 0) := by sorry

end ServiceParts.Shortfall
