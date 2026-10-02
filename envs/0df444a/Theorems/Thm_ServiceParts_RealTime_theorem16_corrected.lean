-- Prove2me | Theorems.Thm_ServiceParts_RealTime_theorem16_corrected
-- name    : ServiceParts.RealTime.theorem16_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T00:30:34.627179+00:00
-- url     : https://prove2.me/theorems/f11bc1d2-5254-44b8-b596-97ff966108d8
-- title:
--   Theorem 16 (corrected) — S̃_ijt ≤ S*_ijt, and S*_ijt ≤ S̃_ijt + M_jt when T^r = T^e + 1 or t < T^e + T_i0
-- statement:
--   Fix an item with a finite set $J$ of bases. For every base $j$ and every period $k \in [T^e_{ij}, \dots, T^r_{ij} + T_{i0}]$ let $\hat S_{ijk}$ be the largest optimal solution of the constrained newsvendor problem $\mathrm{CN}_{ijk}$, and for $t \in [T^e_{ij}, \dots, T^r_{ij} + T_{i0}]$ put
--   $$M_{jt} = \max_{k \in [T^e_{ij}, \dots, t]} \big\{ \hat S_{ijk} - \tilde S_{ijk} \big\}. \tag{10.43}$$
--   Let $S^*_{ijt}$ be the cumulative supply of an optimal solution of $\mathrm{ESAM}_i$. Then for every base $j$ and every $t \in [T^e_{ij}, \dots, T^r_{ij} + T_{i0}]$:
--
--   1. $\tilde S_{ijt} \le S^*_{ijt}$;
--   2. if $T^r_{ij} = T^e_{ij} + 1$ or $t < T^e_{ij} + T_{i0}$, then
--   $$S^*_{ijt} \le \tilde S_{ijt} + M_{jt}. \tag{10.44}$$
--
--   These bounds confine the optimal cumulative stock levels of the model with expedited shipments to a finite window, which the book uses to write $\mathrm{ESAM}_i$ as a linear program.
--
--   **Formalization Note** This corrects the book's Theorem 16, which asserts the upper bound for every $t$ with no proviso. As printed it is false. When $T^r_{ij} \ge T^e_{ij} + 2$, an expedited unit shipped in the last period $T_{i0}$ arrives in period $T^e_{ij} + T_{i0}$ and cannot be shipped later. It may still be worth sending to cover demand in a later period, which pushes $S^*$ above $\tilde S + M$; the item `theorem16_counterexample` gives an instance. The book's exchange argument delays the last arriving unit by one period. That argument is valid when the violating period precedes $T^e_{ij} + T_{i0}$. It is also valid when $T^r_{ij} = T^e_{ij} + 1$, where a last-period expedited unit can be replaced by a regular one arriving one period later.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 244, Theorem 16, (10.43)-(10.44) (corrected: the book states the upper bound without the proviso)

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_ESAM

open MeasureTheory

namespace ServiceParts.RealTime

/-- Theorem 16, p. 244, corrected. Let `Ŝ_{ijk}` be the largest optimal solution of
`CN_{ijk}` for `k ∈ [T^e_{ij}, …, T^r_{ij} + T_{i0}]` and
`M_{jt} = max_{k∈[T^e_{ij},…,t]} {Ŝ_{ijk} - S̃_{ijk}}` (10.43). In every optimal solution of
`ESAM_i`, for every base `j` and `t ∈ [T^e_{ij}, …, T^r_{ij} + T_{i0}]`,
`S̃_{ijt} ≤ S*_{ijt}`, and `S*_{ijt} ≤ S̃_{ijt} + M_{jt}` (10.44) provided
`T^r_{ij} = T^e_{ij} + 1` or `t < T^e_{ij} + T_{i0}`. (The upper bound as printed, without
this proviso, is false: see `theorem16_counterexample`.) -/
theorem theorem16_corrected {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j t ≤ esamStock M yr ye j t ∧
      (M.Tr j = M.Te j + 1 ∨ t < M.Te j + M.T0 →
        esamStock M yr ye j t ≤ M.baseSupply j t +
          (Finset.Icc (M.Te j) t).sup' ⟨M.Te j, Finset.left_mem_Icc.mpr ht₁⟩
            (fun k => Shat j k - M.baseSupply j k)) := by sorry

end ServiceParts.RealTime
