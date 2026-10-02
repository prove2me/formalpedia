-- Prove2me | Theorems.Thm_ServiceParts_RealTime_largest_cn_solution_mono
-- name    : ServiceParts.RealTime.largest_cn_solution_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T00:12:53.258704+00:00
-- url     : https://prove2.me/theorems/3674a00e-9a0a-430d-b4eb-eb91d619e15f
-- title:
--   Eq. (10.20) — Ŝ_ij(t−1) ≤ Ŝ_ijt on the regular-shipment window
-- statement:
--   Fix a base $j$ and a period $t$ with $T^r_{ij} \le t \le T^r_{ij} + T_{i0}$. If $\hat S_{ij(t-1)}$ and $\hat S_{ijt}$ are the largest optimal solutions of the constrained newsvendor problems $\mathrm{CN}_{ij(t-1)}$ and $\mathrm{CN}_{ijt}$, then
--   $$\hat S_{ij(t-1)} \le \hat S_{ijt}. \tag{10.20}$$
--
--   On this window the lower bounds coincide, $\tilde S_{ij(t-1)} = \tilde S_{ijt}$. The cumulative demand grows with $t$, so the newsvendor solutions can only move up. The book uses (10.20) in the proof of Theorem 15.
--
--   **Formalization Note** "Cumulative demand" is the item-model field requiring $X_{ijt}$ to be nondecreasing in $t$ for every outcome. The book derives from it that the distribution functions decrease in $t$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 237, Eq. (10.20)

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

/-- Eq. (10.20), p. 237: for `t ∈ [T^r_{ij}, …, T^r_{ij} + T_{i0}]`, the largest optimal
solutions of the constrained newsvendor problems satisfy `Ŝ_{ij(t-1)} ≤ Ŝ_{ijt}`. -/
theorem largest_cn_solution_mono {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) (s s' : ℤ)
    (hs : M.IsLargestCNSolution j (t - 1) s) (hs' : M.IsLargestCNSolution j t s') :
    s ≤ s' := by sorry

end ServiceParts.RealTime
