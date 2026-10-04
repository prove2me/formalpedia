-- Prove2me | Theorems.Thm_SeatInventory_Distinct_emsr_optimality_conditions
-- name    : SeatInventory.Distinct.emsr_optimality_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:05:38.525807+00:00
-- url     : https://prove2.me/theorems/9fd16df0-34a2-4a5e-981a-c71b1876354e
-- title:
--   Eq. (5.13), discrete form — EMSR optimality conditions for distinct fare classes
-- statement:
--   Let fare classes $i$ have fares $f_i \ge 0$ and integer-valued requests $r_i$, write $\mathrm{EMSR}_i(S) = f_i\cdot P[r_i\ge S]$, and let $S = (S_i)$ be an allocation of exactly $C$ seats, $\sum_i S_i = C$, to distinct fare-class inventories. Then $S$ maximises the total expected revenue $\bar R = \sum_i f_i\, E[\min(r_i,S_i)]$ among all allocations of exactly $C$ seats if and only if there is a number $\lambda$ with
--   $$
--   \mathrm{EMSR}_i(S_i) \ \ge\ \lambda\ \ \text{whenever } S_i \ge 1, \qquad \mathrm{EMSR}_i(S_i+1)\ \le\ \lambda, \qquad \text{for every class } i .
--   $$
--
--   This is the integer counterpart of the thesis's Lagrangian condition $\mathrm{EMSR}_i(S_i^*) = \lambda$ for all $i$: the value of the last seat given to any class is at least the value of the next seat of any class, so no transfer of a seat between classes raises expected revenue. It covers the "corner" solutions the thesis mentions, in which some class receives no seats.
--
--   **Formalization Note** The thesis's equality "$= \lambda$" is the first-order condition of the continuous relaxation; with integer seats exact equality generally fails, so the discrete reading brackets $\lambda$ between the last allocated and the next unallocated seat. Requests are a `PMF ℕ` and $P[r\ge S]$ is used throughout. Fares are assumed nonnegative.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 107, Eq. (5.13); see also p. 105, Eq. (5.12), and p. 86, Eqs. (4.3)-(4.4)

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (5.13), p. 107 (with (5.12), p. 105, and (4.3)–(4.4), p. 86), discrete
reading: an allocation `S` of exactly `C` seats to distinct fare-class inventories maximises total
expected revenue among all allocations of `C` seats iff there is a `λ` lying between the EMSR
of the last seat allocated to each class and the EMSR of the next seat of each class:
`EMSR_i(S_i) ≥ λ` whenever `S_i ≥ 1`, and `EMSR_i(S_i + 1) ≤ λ`, for every class `i`.
Fares are nonnegative. -/
theorem emsr_optimality_conditions {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (d : ι → PMF ℕ) (C : ℕ) (S : ι → ℕ) (hS : ∑ i, S i = C) :
    (∀ S' : ι → ℕ, ∑ i, S' i = C → totalExpectedRevenue f d S' ≤ totalExpectedRevenue f d S) ↔
      ∃ lam : ℝ, ∀ i, (1 ≤ S i → lam ≤ emsr (f i) (d i) (S i)) ∧
        emsr (f i) (d i) (S i + 1) ≤ lam := by sorry

end SeatInventory.Distinct
