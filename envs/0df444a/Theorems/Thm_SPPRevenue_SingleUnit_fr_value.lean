-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_fr_value
-- name    : SPPRevenue.SingleUnit.fr_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:59.057539+00:00
-- url     : https://prove2.me/theorems/535f5f3d-0c59-4da7-b2d0-1d97dae93c40
-- title:
--   §4.1, p. 15, Solving Problem (FR) — the optimal value of (FR) is 1 + ln(τ⋆) ≤ 1.5283
-- statement:
--   Let $\tau^\star > 1$ satisfy $(1 - e^{-1}) + \int_1^{\tau^\star} (1 - e^{-1/\tau})\,d\tau = 1$. Then the optimal value of the factor-revealing program
--   $$\mathrm{FR} = \max\Big\{\int_0^\infty s(\tau)\,d\tau \ :\ 0 \le s(\tau) \le \min(1, 1/\tau)\ \forall \tau \ge 0,\ \int_0^\infty \big(1 - e^{-s(\tau)}\big)\,d\tau \le 1,\ s \text{ weakly decreasing}\Big\}$$
--   is attained and equals $1 + \ln \tau^\star$, and $1 + \ln \tau^\star \le 1.5283$.
--
--   This is the value that yields the constant $1/1.5283 \approx 0.6543$ of Theorem 1.
--
--   **Formalization Note** The paper prints $1 + \ln(\tau^\star) = 1.5283$, which is $1 + \ln(1.696)$ with the rounded $\tau^\star$; with the exact root the value is $1.52810\ldots$. The theorem states the exact value $1 + \ln\tau^\star$ and the upper bound $1.5283$, which is what the constant $0.6543$ requires. "Attained and equal" is stated as: $1 + \ln\tau^\star$ is the greatest element of the set of objective values of feasible $s$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 15, §4.1, Solving Problem (FR)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem fr_value (T : ℝ) (hT : 1 < T) (hroot : frRootEq T) :
    IsGreatest {x : ℝ≥0∞ | ∃ s : ℝ → ℝ, FRFeasible s ∧ x = frObj s}
        (ENNReal.ofReal (1 + Real.log T)) ∧
      1 + Real.log T ≤ 15283 / 10000 := by sorry

end SPPRevenue.SingleUnit
