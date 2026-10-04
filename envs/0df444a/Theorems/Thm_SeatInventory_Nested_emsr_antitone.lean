-- Prove2me | Theorems.Thm_SeatInventory_Nested_emsr_antitone
-- name    : SeatInventory.Nested.emsr_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:45:41.965213+00:00
-- url     : https://prove2.me/theorems/0b7e0b5c-08bb-4e8d-b062-d82a0fcf9986
-- title:
--   Eqs. (6.1)–(6.2) — $P[r\ge S]$ and $\mathrm{EMSR}(S)$ are non-increasing in $S$
-- statement:
--   Let $r$ be an $\mathbb N$-valued demand on a probability space and $f \ge 0$ a fare. Then
--   $$S \le S' \implies P[r \ge S'] \le P[r \ge S] \quad\text{and}\quad \mathrm{EMSR}(S') = f\,P[r \ge S'] \le f\,P[r \ge S] = \mathrm{EMSR}(S).$$
--
--   The thesis records this on p. 142 as the reason "virtually any probability density function will work in the EMSR formulations": because $\mathrm{EMSR}(S)$ decreases in $S$, the set of protection levels satisfying (5.15) is an initial segment of $\{0, \dots, C\}$.
--
--   **Formalization Note** "Decreasing" in the thesis means non-increasing; the fare is assumed nonnegative, as all fares in the thesis are.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 142, Eqs. (6.1)-(6.2)

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

namespace SeatInventory.Nested

open MeasureTheory

theorem emsr_antitone {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → ℕ) (f : ℝ) (hf : 0 ≤ f) :
    Antitone (tailProb μ r) ∧ Antitone (emsr μ r f) := by sorry

end SeatInventory.Nested
