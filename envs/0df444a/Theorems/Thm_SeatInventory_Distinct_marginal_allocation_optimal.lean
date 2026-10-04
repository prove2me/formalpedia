-- Prove2me | Theorems.Thm_SeatInventory_Distinct_marginal_allocation_optimal
-- name    : SeatInventory.Distinct.marginal_allocation_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:23:49.519112+00:00
-- url     : https://prove2.me/theorems/d78f1374-1f13-493a-bce0-e391ccf4bc31
-- title:
--   Sect. 4.2, p. 90 — the n largest m_i(k) give the revenue-maximising booking limits
-- statement:
--   A flight leg with $n$ seats serves fare classes $i$ with average fares $f_i\ge 0$ and integer-valued requests $r_i$, each class with its own distinct seat inventory. Let $m_i(k) = f_i\cdot P[r_i\ge k]$ be the expected marginal revenue of the $k$-th seat of class $i$, $1\le k\le n$, and let $T$ be any set of $n$ pairs $(i,k)$ carrying $n$ largest values $m_i(k)$ across all classes. Define the booking limits $S^T_i = \#\{k : (i,k)\in T\}$. Then $\sum_i S^T_i = n$, and for every allocation $S$ with $\sum_i S_i \le n$,
--   $$
--   \sum_i f_i\, E[\min(r_i, S_i)] \ \le\ \sum_i f_i\, E[\min(r_i, S^T_i)] .
--   $$
--
--   This is the marginal approach to distinct seat allocation: since $m_i(k)$ decreases in $k$, ranking all (class, seat) marginal values and keeping the $n$ largest determines the revenue-maximising combination of fare-class booking limits.
--
--   **Formalization Note** Expected revenue is computed from the booking rule $\min(r_i,S_i)$, not postulated as a sum of marginal values, and $T$ ranges over every set of $n$ largest values (ties allowed), not a particular sort. Seat numbers start at $1$. Discrete reading: requests are a `PMF ℕ` and $P[r\ge k]$ is used. Fares are assumed nonnegative; the competing allocations may use fewer than $n$ seats.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 90, Sect. 4.2, last paragraph (with the definition of m_i(k) on the same page)

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel
import Definitions.Def_SeatInventory_Distinct_MarginalAllocation

namespace SeatInventory.Distinct

/-- Belobaba 1987, Sect. 4.2, p. 90: since `m_i(k)` decreases in `k`, the `n` largest values
`m_i(k)` across all fare classes determine the revenue-maximising booking limits. For every set
`T` of `n` largest values of `m_i(k) = f_i · P[r_i ≥ k]` over (class, seat) pairs with
`1 ≤ k ≤ n`, the allocation `S^T_i = #{k : (i, k) ∈ T}` uses exactly `n` seats and its total
expected revenue `Σ_i f_i · E[min(r_i, S_i)]` is at least that of every allocation `S` of at
most `n` seats to distinct fare-class inventories. Fares are nonnegative. -/
theorem marginal_allocation_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (d : ι → PMF ℕ) (n : ℕ) (T : Finset (ι × ℕ))
    (hT : IsTopN (marginalRevenue f d) (seatPairs ι n) T n) :
    ∑ i, allocationOf T i = n ∧
    ∀ S : ι → ℕ, ∑ i, S i ≤ n →
      totalExpectedRevenue f d S ≤ totalExpectedRevenue f d (allocationOf T) := by sorry

end SeatInventory.Distinct
