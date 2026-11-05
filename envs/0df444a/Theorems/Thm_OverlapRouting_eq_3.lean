-- Prove2me | Theorems.Thm_OverlapRouting_eq_3
-- name    : OverlapRouting.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:50.85798+00:00
-- url     : https://prove2.me/theorems/86b06f9a-0819-4a89-b0b5-e5450f897e00
-- title:
--   Display (3) — under Algorithm 1 vehicle $j$ makes $r_j=\lceil w_j/Q\rceil$ trips
-- statement:
--   Let $Q\ge1$, let $d$ be any vector of nonnegative integer demands on the labels, and let $1\le j\le M$. With $e_0=0$, $w_j=(\bar d_j-e_{j-1})^+$, $r_j=\lceil w_j/Q\rceil$, $e_j=Qr_j-w_j$ and $e'_j$ as in Algorithm 1, the route that Algorithm 1 drives for vehicle $j$ satisfies:
--
--   1. vehicle $j$ leaves the depot exactly $r_j=\lceil w_j/Q\rceil$ times;
--   2. each of its trips delivers at least one and at most $Q$ units;
--   3. it delivers exactly $w_j$ units on $\mathcal N_j$ and exactly $e'_j$ units on $\mathcal N_{j+1}$;
--   4. $w_j+e'_j\le Qr_j$;
--
--   and the $M$ vehicles together deliver exactly $d_i$ to every customer $i$.
--
--   This ties the trip count $r_j$ of (3), which defines $\mathbb E[R_j]$, to the routes whose length is $Z^{AO(\alpha)}$.
--
--   Differences from the source:
--   - generalization: "By Algorithm 1, given a demand instance d, we have e₀ = 0, wⱼ = (d̄ⱼ − eⱼ₋₁)⁺, rⱼ = ⌈wⱼ/Q⌉, eⱼ = Qrⱼ − wⱼ" → the number of trips of the driven route equals ⌈wⱼ/Q⌉, plus: every trip carries 1 to Q units, vehicle j delivers wⱼ units on 𝒩ⱼ and e′ⱼ on 𝒩ⱼ₊₁, wⱼ + e′ⱼ ≤ Qrⱼ, and all demand is delivered; reason: the extra clauses are the content of Algorithm 1, line 13 and p.10 that (3) summarizes; dropping them gives (3)
--   - generalization: demands with values in {0,…,u} → any nonnegative integer demands; reason: the recursion does not use the bound u; specializes
--   - encoding: customers labelled 1,…,N along the tour, vehicles j = 1,…,M → 0-based labels 0,…,N′M−1 given by a permutation ℓ (label k is customer ℓ k); 1-based vehicle indices; reason: Lean convention; same instances
--   - encoding: the variables sⱼ and d′_{sⱼ} of Algorithm 1 (lines 2, 5, 9, 11) → the amount vehicle j delivers to i ∈ 𝒩ⱼ₊₁ is min(dᵢ, (e′ⱼ − Σ_{k∈𝒩ⱼ₊₁, k<i} d_k)⁺); reason: the same split: vehicle j takes the first e′ⱼ units of 𝒩ⱼ₊₁ in label order and sⱼ₊₁ is where it stops short (checked on a concrete day)
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, display (3), p.14; Algorithm 1, p.11; rules of p.10

import Mathlib
import Definitions.Def_OverlapRouting_costAO

namespace OverlapRouting

/-- **Display (3)**, p.14 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)): "By Algorithm 1,
given a demand instance `d`, we have `e₀ = 0`, `wⱼ = (d̄ⱼ − eⱼ₋₁)⁺`, `rⱼ = ⌈wⱼ/Q⌉`,
`eⱼ = Qrⱼ − wⱼ`."

For every capacity `Q ≥ 1`, every demand vector on the labels and every vehicle `1 ≤ j ≤ M`, the
route that Algorithm 1 drives for vehicle `j`:
1. leaves the depot exactly `rⱼ = ⌈wⱼ/Q⌉` times;
2. every trip delivers at least one and at most `Q` units;
3. delivers exactly `wⱼ` units on its primary route `𝒩ⱼ` and exactly `e′ⱼ` units on `𝒩ⱼ₊₁`;
4. `wⱼ + e′ⱼ ≤ Q rⱼ`;
and the `M` vehicles together deliver exactly the demand of every customer.

**Formalization Note.** Labels are 0-based, vehicles 1-based; `excess`, `workload`, `trips`,
`usedExcess` are `eⱼ`, `wⱼ`, `rⱼ`, `e′ⱼ` defined by the recursion (3) and Algorithm 1, lines 1 and 4.
The trips are those of `vehicleTrips` (refill exactly at a stock-out). -/
theorem eq_3 (N' Q M : ℕ) (hQ : 1 ≤ Q) (dem : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjM : j ≤ M) :
    (vehicleTrips N' Q M dem j).length = trips N' Q dem j ∧
    (∀ t ∈ vehicleTrips N' Q M dem j, t ≠ [] ∧ t.length ≤ Q) ∧
    ((unitLabels N' Q M dem j).filter (fun i => i ∈ primaryRoute N' j)).length =
      workload N' Q dem j ∧
    ((unitLabels N' Q M dem j).filter (fun i => i ∈ primaryRoute N' (j + 1))).length =
      usedExcess N' Q M dem j ∧
    workload N' Q dem j + usedExcess N' Q M dem j ≤ Q * trips N' Q dem j ∧
    (∀ i < N' * M, ∑ k ∈ Finset.Icc 1 M, served N' Q M dem k i = dem i) := by sorry

end OverlapRouting
