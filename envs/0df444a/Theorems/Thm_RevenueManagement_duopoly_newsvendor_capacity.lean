-- Prove2me | Theorems.Thm_RevenueManagement_duopoly_newsvendor_capacity
-- name    : RevenueManagement.duopoly_newsvendor_capacity
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:04:40.507985+00:00
-- url     : https://prove2.me/theorems/1135e39c-7b6b-4f35-aeff-a8ae13522935
-- title:
--   Example 8.16: in the duopoly newsvendor game with demand spillover, the equilibrium capacities satisfying (8.23) total at least the monopoly newsvendor capacity
-- statement:
--   Let the native demands $D_1, D_2$ be measurable, $0 < c < r$, $x^*$ the monopoly
--   newsvendor quantity for the aggregate demand $D = D_1 + D_2$, $\mathbb P(D > x^*) = c/r$,
--   with $\mathbb P(D > x)$ strictly larger for every $x < x^*$ (the c.d.f. of $D$ is
--   strictly increasing), and let $(x_1^*, x_2^*)$ satisfy the equilibrium conditions (8.23),
--   $\mathbb P(R_i(x^*) \le x_i^*) = 1 - c/r$ for the effective demands
--   $R_1 = D_1 + (D_2 - x_2^*)^+$ and $R_2 = D_2 + (D_1 - x_1^*)^+$. Then
--   $x_1^* + x_2^* \ge x^*$.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 379-380, Example 8.16 with Eq. (8.23) ('So we must have x1* + x2* ≥ x*; the total duopoly capacity is therefore at least as large as the monopoly capacity')

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem duopoly_newsvendor_capacity (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (c r : ℝ) (hc : 0 < c) (hcr : c < r)
    (xstar x1 x2 : ℝ) (hmono : P {ω | xstar < D1 ω + D2 ω} = ENNReal.ofReal (c / r))
    (hstrict : ∀ x, x < xstar → P {ω | xstar < D1 ω + D2 ω} < P {ω | x < D1 ω + D2 ω})
    (h1 : P {ω | effectiveDemand D1 D2 x2 ω ≤ x1} = ENNReal.ofReal (1 - c / r))
    (h2 : P {ω | effectiveDemand D2 D1 x1 ω ≤ x2} = ENNReal.ofReal (1 - c / r)) :
    xstar ≤ x1 + x2 := by sorry

end RevenueManagement
