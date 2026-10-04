-- Prove2me | Theorems.Thm_SeatInventory_Distinct_lp_top_n_optimal
-- name    : SeatInventory.Distinct.lp_top_n_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:23:42.692027+00:00
-- url     : https://prove2.me/theorems/4e5b978b-79d0-4846-b471-eb5a4d952b78
-- title:
--   Eq. (4.5) — the indicator of the n largest m_i(k) solves the seat-allocation LP
-- statement:
--   Let a leg have capacity $n$ and fare classes $i$ with fares $f_i \ge 0$ and integer-valued request laws, and let $m_i(k) = f_i\cdot P[r_i \ge k]$ for $k\in\{1,\dots,n\}$. Consider the linear program
--   $$
--   \max\ \bar R(n) = \sum_i \sum_{k=1}^{n} X_{ik}\, m_i(k)\quad\text{subject to}\quad \sum_i\sum_k X_{ik} \le n,\qquad 0\le X_{ik}\le 1 .
--   $$
--   Let $T$ be any set of $n$ pairs $(i,k)$ carrying $n$ largest values of $m_i(k)$. Then the 0–1 vector with $X_{ik} = 1$ for $(i,k)\in T$ and $X_{ik}=0$ otherwise is feasible, and its objective value is at least that of every feasible $X$: the program has an integer optimal solution given by the $n$ largest $m_i(k)$.
--
--   This is the LP formulation of the single-leg seat-allocation problem with probabilistic demand surveyed in Sect. 4.2; its integrality is what lets a simple ranking replace a general LP solver.
--
--   **Formalization Note** When several pairs tie in value, the LP may also have fractional optimal solutions, so "the solution will be integer" is stated as: the indicator of every set of $n$ largest values is optimal. Fares are assumed nonnegative, which makes every $m_i(k) \ge 0$; with a negative value the inequality $\sum X_{ik}\le n$ would not bind. Discrete reading of $P[r\ge k]$ as in the demand model.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 90, Eq. (4.5) and the sentence following it

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel
import Definitions.Def_SeatInventory_Distinct_MarginalAllocation

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (4.5) and the sentence after it, p. 90: for the linear program
maximising `Σ_i Σ_k X_ik · m_i(k)` over `(i, k) ∈ classes × {1, …, n}` subject to
`Σ X_ik ≤ n`, `0 ≤ X_ik ≤ 1`, the 0–1 vector equal to `1` exactly on a set `T` of `n` largest
values `m_i(k)` is feasible and optimal. Fares are nonnegative. -/
theorem lp_top_n_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (d : ι → PMF ℕ) (n : ℕ) (T : Finset (ι × ℕ))
    (hT : IsTopN (marginalRevenue f d) (seatPairs ι n) T n) :
    IsLPFeasible (seatPairs ι n) n (fun a => if a ∈ T then (1 : ℝ) else 0) ∧
    ∀ X : ι × ℕ → ℝ, IsLPFeasible (seatPairs ι n) n X →
      lpObjective (marginalRevenue f d) (seatPairs ι n) X ≤
        lpObjective (marginalRevenue f d) (seatPairs ι n)
          (fun a => if a ∈ T then (1 : ℝ) else 0) := by sorry

end SeatInventory.Distinct
