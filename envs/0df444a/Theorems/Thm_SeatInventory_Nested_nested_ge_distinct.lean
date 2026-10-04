-- Prove2me | Theorems.Thm_SeatInventory_Nested_nested_ge_distinct
-- name    : SeatInventory.Nested.nested_ge_distinct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:46:04.047877+00:00
-- url     : https://prove2.me/theorems/18f2638c-7fd8-4b91-a35f-88bb12278236
-- title:
--   Sect. 5.2, p. 114 — nested inventories earn at least as much as distinct ones with the same $BL_2$
-- statement:
--   Let $r_1, r_2$ be measurable $\mathbb N$-valued demands on a probability space, $f_1 \ge 0$, $f_2 \in \mathbb R$, and $S \le C$. Compare the nested inventory with class-2 booking limit $C - S$ (class 2 books first, class 1 may use every unsold seat) with two distinct inventories of $S$ class-1 seats and $C - S$ class-2 seats. Then
--   $$\mathbb E[R^{\mathrm{dist}}_S] \le \mathbb E[R^{\mathrm{nest}}_S],$$
--   and if moreover $f_1 > 0$ and
--   $$P\bigl[r_2 < C - S \ \text{and}\ r_1 > S\bigr] > 0,$$
--   the inequality is strict.
--
--   The condition is the thesis's "some probability that not all class 2 seats will be booked by class 2 passengers and that class 1 demand will exceed the class 1 allotment".
--
--   **Formalization Note** The thesis says nested revenue is "generally higher … as long as" the condition holds; this is formalized as the weak inequality in general together with the strict one under the condition. The booking order is low fare first, the assumption under which the thesis makes the comparison (p. 112).
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 114, Sect. 5.2, with the booking-order assumption of p. 112

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

namespace SeatInventory.Nested

open MeasureTheory

theorem nested_ge_distinct {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r₁ r₂ : Ω → ℕ) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (f₁ f₂ : ℝ) (hf₁ : 0 ≤ f₁) (C S : ℕ) (hSC : S ≤ C) :
    expectedDistinctRevenue μ r₁ r₂ f₁ f₂ C S ≤ expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S ∧
      (0 < f₁ → 0 < μ.real {ω | r₂ ω < C - S ∧ S < r₁ ω} →
        expectedDistinctRevenue μ r₁ r₂ f₁ f₂ C S <
          expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S) := by sorry

end SeatInventory.Nested
