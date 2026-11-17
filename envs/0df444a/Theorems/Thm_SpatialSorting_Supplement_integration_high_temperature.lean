-- Prove2me | Theorems.Thm_SpatialSorting_Supplement_integration_high_temperature
-- name    : SpatialSorting.Supplement.integration_high_temperature
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:37:46.226105+00:00
-- url     : https://prove2.me/theorems/b18836de-02ab-45a7-9c65-87239ceec197
-- title:
--   Theorem 2 — integration at high temperature
-- statement:
--   Let $q\ge2$ be a number of colours, $A\in\mathcal A_q$ a cost matrix (symmetric, zero diagonal, positive off-diagonal entries, largest entry $A_{\max}$) and $\rho\in\Delta_{q-1}$ a density vector with positive entries. Consider the fixed-magnetization Generalized Potts Model on the rhombus $D_L$ of the triangular lattice, with collar wired to colour $0$ and prescribed colour counts, and its Gibbs distribution $\pi_{\Lambda^L,\beta,\rho}$; let $N_L=|I_L|$ be the number of free sites.
--
--   Given $c>0$ and $\delta>0$, set
--   $$
--   d=\min\{\delta,1\},\qquad \beta_{\mathrm{high}}=\frac{d^2}{192A_{\max}},\qquad \zeta=e^{-d^2/16}.
--   $$
--   There is $L_0=L_0(c,\delta,q)$, depending only on $c$, $\delta$ and $q$, such that for every $A$, every $\rho$, every $0\le\beta\le\beta_{\mathrm{high}}$ and every $L\ge L_0$,
--   $$
--   \pi_{\Lambda^L,\beta,\rho}\big(\mathrm{Integrated}(c,\delta)\big)\ \ge\ 1-\zeta^{N_L}.
--   $$
--
--   At high temperature colours are spread nearly uniformly: every low-perimeter region carries its fair share of each colour up to $\delta N_L$, with overwhelming probability. Together with Theorem 1 this separates the two temperature regimes (Corollary 1.7).
--
--   **Formalization Note** The dependence $L_0=L_0(c,\delta,q)$ is expressed by the quantifier order: $L_0$ is chosen after $q,c,\delta$ and before $A,\rho,\beta,L$.
--
--   Differences from the source: none.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 2, p. 9 (PDF p. 10); proof §8, pp. 45–47 (PDF pp. 46–48)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_N
import Definitions.Def_SpatialSorting_Supplement_integratedProb
open Classical Filter Topology

namespace SpatialSorting.Supplement

/-- Theorem 2 — integration at high temperature. With `d = min{δ, 1}`, `β_high = d² / (192 A_max)` and
`ζ = e^{−d²/16}`, there is `L_0 = L_0(c, δ, q)` such that for `0 ≤ β ≤ β_high` and `L ≥ L_0`,
`π_{Λ^L,β,ρ}(Integrated(c, δ)) ≥ 1 − ζ^{N_L}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 2, p. 9 (PDF p. 10).

Formalization Notes:
- encoding: `L_0 = L_0(c, δ, q)` → `L_0` is chosen after `q, c, δ` and before `A, ρ, β`; quantifier
  order expresses the dependence.
- encoding: `A_max` is the base `amax A`, positive for `q ≥ 2` and `A ∈ 𝒜_q`; `N_L` is the base `N L`.
- encoding: `ζ^{N_L}` is written `(e^{−d²/16})^{N_L}` with a natural-number power.
- `β` ranges over the closed interval `[0, β_high]` (β = 0 is the uniform law on `Ω_{Λ^L,ρ}`);
  `δ > 0` has no upper bound and `c > 0` is arbitrary, as on the page. -/
theorem integration_high_temperature :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ c δ : ℝ, 0 < c → 0 < δ →
      ∃ L0 : ℕ, ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A →
        ∀ ρ : Fin q → ℝ, IsDensity ρ →
          ∀ β : ℝ, 0 ≤ β → β ≤ (min δ 1) ^ 2 / (192 * amax A) →
            ∀ L : ℕ, L0 ≤ L →
              1 - Real.exp (-((min δ 1) ^ 2 / 16)) ^ (N L) ≤ integratedProb A β ρ L c δ := by sorry

end SpatialSorting.Supplement
