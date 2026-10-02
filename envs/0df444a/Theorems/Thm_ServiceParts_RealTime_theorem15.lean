-- Prove2me | Theorems.Thm_ServiceParts_RealTime_theorem15
-- name    : ServiceParts.RealTime.theorem15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T00:40:18.946653+00:00
-- url     : https://prove2.me/theorems/1524a0b8-cf27-4ba9-bd08-87a3dab8ed3e
-- title:
--   Theorem 15 — optimal SAM_i stock levels satisfy S̃_ij(T^r−1) ≤ S*_ijt ≤ Ŝ_ijt
-- statement:
--   Fix an item with a finite set $J$ of bases. For every base $j$ and every period $t \in [T^r_{ij}, \dots, T^r_{ij} + T_{i0}]$ let $\hat S_{ijt}$ be the largest optimal solution of the constrained newsvendor problem $\mathrm{CN}_{ijt}$. That is, $\hat S_{ijt}$ is the largest minimizer of the single-period cost $G_{ijt}(S) = h_{ij} E[S - X_{ijt}]^+ + b_{ij} E[X_{ijt} - S]^+$ over integers $S \ge \tilde S_{ijt}$. Let $S^*_{ijt}$ be the cumulative supply at base $j$ through period $t$ in an optimal solution of the stock allocation model $\mathrm{SAM}_i$. Then
--   $$\tilde S_{ij(T^r_{ij}-1)} \le S^*_{ijt} \le \hat S_{ijt} \qquad \forall j \in J,\ t \in [T^r_{ij}, \dots, T^r_{ij} + T_{i0}]. \tag{10.21}$$
--
--   The theorem holds for every optimal solution. It confines the optimal cumulative stock at each base to a window computed from single-period newsvendor problems alone. The book uses this window to reformulate $\mathrm{SAM}_i$ as a linear program in 0–1 variables $\delta_{ijtk}$ indexed by the stock levels in the window.
--
--   **Formalization Note** $\hat S_{ijt}$ enters as a function `Shat` with the hypothesis that each value is the largest optimal solution of $\mathrm{CN}_{ijt}$. Such values exist and are unique (item `largest_cn_solution`). Nonnegativity and integrality of the shipments are built into their type.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 237, Theorem 15, (10.21)

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_SAM

open MeasureTheory

namespace ServiceParts.RealTime

/-- Theorem 15, p. 237: let `Ŝ_{ijt}` be the largest optimal solution of `CN_{ijt}` for
`t ∈ [T^r_{ij}, …, T^r_{ij} + T_{i0}]`. In every optimal solution of `SAM_i`, the cumulative
supply satisfies `S̃_{ij(T^r_{ij}-1)} ≤ S*_{ijt} ≤ Ŝ_{ijt}` (10.21) for all bases `j` and all
`t ∈ [T^r_{ij}, …, T^r_{ij} + T_{i0}]`. -/
theorem theorem15 {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (y : J → ℕ → ℕ) (hy : IsSAMOptimal M y) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j (M.Tr j - 1) ≤ samStock M y j t ∧ samStock M y j t ≤ Shat j t := by sorry

end ServiceParts.RealTime
