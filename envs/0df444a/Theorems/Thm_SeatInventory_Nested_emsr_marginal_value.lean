-- Prove2me | Theorems.Thm_SeatInventory_Nested_emsr_marginal_value
-- name    : SeatInventory.Nested.emsr_marginal_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:45:28.42873+00:00
-- url     : https://prove2.me/theorems/867468ea-1ed9-4f9b-9388-4b4fefe77ad3
-- title:
--   Eq. (5.11) — adding the S-th seat raises expected class revenue by $f\cdot P[r\ge S]$
-- statement:
--   Let $r$ be an $\mathbb N$-valued measurable demand on a probability space and $f$ a fare. Write $\bar R(S) = f\,\mathbb E[\min(r, S)]$ for the expected revenue of $S$ seats in that fare class and $\mathrm{EMSR}(S) = f \cdot P[r \ge S]$. Then for every $S \ge 1$,
--   $$\bar R(S) - \bar R(S-1) = \mathrm{EMSR}(S) = f \cdot P[r \ge S].$$
--
--   This identifies the expected marginal seat revenue of the $S$-th seat as the average fare times the probability of selling $S$ or more seats, Eq. (5.11) of the thesis; it is the quantity compared with $f_2$ in the EMSR rule.
--
--   **Formalization Note** The thesis defines $\mathrm{EMSR}_i$ as the derivative $\partial \bar R/\partial S_i$ of a continuous model; with integer seats the derivative is the forward difference above. Eq. (5.11) is also a milestone of mission I of this series; it is restated here in the namespace `SeatInventory.Nested`.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 105, Eq. (5.11), with Eq. (5.14), p. 109

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

namespace SeatInventory.Nested

open MeasureTheory

theorem emsr_marginal_value {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → ℕ) (hr : Measurable r) (f : ℝ) (S : ℕ) (hS : 1 ≤ S) :
    classRevenue μ r f S - classRevenue μ r f (S - 1) = emsr μ r f S := by sorry

end SeatInventory.Nested
