-- Prove2me | Theorems.Thm_SeatInventory_Nested_emsr_protection_level_optimal
-- name    : SeatInventory.Nested.emsr_protection_level_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:46:15.735232+00:00
-- url     : https://prove2.me/theorems/e6005eb5-e706-4220-b85d-f5f0e3e7b413
-- title:
--   Eqs. (5.15)–(5.16) — the EMSR protection level maximises expected revenue for two nested fare classes
-- statement:
--   Consider a single flight leg with capacity $C \in \mathbb N$ and two nested fare classes with fares $0 \le f_2 \le f_1$. Requests $r_1, r_2$ are independent measurable $\mathbb N$-valued random variables on a probability space, and all class-2 requests arrive before any class-1 request. A protection level $S \in \{0, \dots, C\}$ sets the class-2 booking limit $C - S$, and the expected revenue is
--   $$\bar R(S) = \mathbb E\Bigl[f_2 \min(r_2, C - S) + f_1 \min\bigl(r_1,\, C - \min(r_2, C - S)\bigr)\Bigr].$$
--   Let $S_2^1$ be the EMSR protection level of Eq. (5.15): the largest integer $S \in \{0, \dots, C\}$ such that
--   $$\mathrm{EMSR}_1(S) = f_1 \cdot P[r_1 \ge S] \ge f_2.$$
--   Then $S_2^1 \le C$ and
--   $$\bar R(S) \le \bar R(S_2^1) \qquad \text{for every } S \in \{0, \dots, C\}.$$
--
--   This is the thesis's central two-class result: the protection level found by comparing the expected marginal seat revenue of class 1 with the class-2 fare maximises expected revenue under static seat inventory control, and it does not depend on the class-2 demand distribution.
--
--   **Formalization Note** Demands are $\mathbb N$-valued and $\bar P_1(S) = P[r_1 \ge S]$ (Eq. (6.2) and the prose of (5.11)); with $P[r_1 > S]$ as in Eq. (5.2) the rule would be off by one seat. Eq. (5.16)'s equality $\mathrm{EMSR}_1(S_2^1) = f_2$ is the continuous idealisation of (5.15) and is not stated. The thesis assumes $f_1 > f_2$; the statement allows $f_1 = f_2$.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 109, Eqs. (5.15)-(5.16), and p. 112 ('This solution will maximize expected revenues ... (static seat inventory control)')

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

namespace SeatInventory.Nested

open MeasureTheory ProbabilityTheory

theorem emsr_protection_level_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r₁ r₂ : Ω → ℕ) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (hind : IndepFun r₁ r₂ μ) (f₁ f₂ : ℝ) (hf₂ : 0 ≤ f₂) (hf : f₂ ≤ f₁) (C : ℕ) :
    emsrProtectionLevel μ r₁ f₁ f₂ C ≤ C ∧
      ∀ S ≤ C, expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S ≤
        expectedNestedRevenue μ r₁ r₂ f₁ f₂ C (emsrProtectionLevel μ r₁ f₁ f₂ C) := by sorry

end SeatInventory.Nested
