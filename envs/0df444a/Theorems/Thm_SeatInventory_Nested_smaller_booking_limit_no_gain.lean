-- Prove2me | Theorems.Thm_SeatInventory_Nested_smaller_booking_limit_no_gain
-- name    : SeatInventory.Nested.smaller_booking_limit_no_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:45:54.098854+00:00
-- url     : https://prove2.me/theorems/d3ca871c-c636-45ec-92ba-d114fb3a5e3e
-- title:
--   Sect. 5.2, p. 112 — making $BL_2$ smaller than $C - S^*$ cannot increase expected revenue
-- statement:
--   Consider the two-class nested model: capacity $C$, fares $0 \le f_2 \le f_1$, independent measurable $\mathbb N$-valued demands $r_1, r_2$ on a probability space, all class-2 requests arriving before any class-1 request. Let $S^* = S_2^1$ be the EMSR protection level, the largest $S \in \{0, \dots, C\}$ with $f_1 P[r_1 \ge S] \ge f_2$, and let $\bar R(S)$ be the expected nested revenue with protection level $S$ (class-2 booking limit $BL_2 = C - S$). Then for every $S$ with $S^* \le S \le C$,
--   $$\bar R(S) \le \bar R(S^*).$$
--
--   That is, protecting more seats than $S^*$ for class 1 (a smaller class-2 booking limit) never raises expected revenue: the thesis argues that every class-1 seat beyond $S^*$ has expected marginal revenue below $f_2$. This is one half of the optimality of $S^*$.
--
--   **Formalization Note** Demands are $\mathbb N$-valued and $\bar P_1(S) = P[r_1 \ge S]$ (Eq. (6.2)). The thesis assumes $f_1 > f_2$; the statement allows $f_1 = f_2$. Independence of $r_1$ and $r_2$ is the thesis's standing assumption of p. 108.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 112, Sect. 5.2 ('Total expected revenues therefore cannot be increased by making BL_2 smaller'), with Eq. (5.15), p. 109

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

namespace SeatInventory.Nested

open MeasureTheory ProbabilityTheory

theorem smaller_booking_limit_no_gain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r₁ r₂ : Ω → ℕ) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (hind : IndepFun r₁ r₂ μ) (f₁ f₂ : ℝ) (hf₂ : 0 ≤ f₂) (hf : f₂ ≤ f₁) (C S : ℕ)
    (hS : emsrProtectionLevel μ r₁ f₁ f₂ C ≤ S) (hSC : S ≤ C) :
    expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S ≤
      expectedNestedRevenue μ r₁ r₂ f₁ f₂ C (emsrProtectionLevel μ r₁ f₁ f₂ C) := by sorry

end SeatInventory.Nested
