-- Prove2me | Theorems.Thm_RankRobustAssort_exists_optimal_mem_SHat
-- name    : RankRobustAssort.exists_optimal_mem_SHat
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:36.008434+00:00
-- url     : https://prove2.me/theorems/f9b01696-c26a-4e39-883e-a739e5de1120
-- title:
--   Theorem 1 — some assortment in $\widehat{\mathcal S}$ is optimal for (RO)
-- statement:
--   Consider a firm with products $\mathcal N_0=\{0,1,\dots,n\}$ (0 the no-purchase option) and revenues $0=r_0<r_1<\dots<r_n$, past assortments $S_1,\dots,S_M\subseteq\mathcal N_0$ with normalized purchase frequencies $v_{m,i}$, a radius $\eta\ge0$ and an $\ell_1$ or $\ell_\infty$ error norm, and suppose the set $\mathcal U$ of ranking-based choice models consistent with the data is nonempty. Then there exists an assortment
--
--   $$
--   S\in\widehat{\mathcal S}\quad\text{with}\quad \min_{\lambda\in\mathcal U}\mathcal R^\lambda(S')\le\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)\ \text{ for every } S'\in\mathcal S,
--   $$
--
--   that is, an assortment revenue-ordered relative to the past assortments that is optimal for the robust problem (RO) $\max_{S\in\mathcal S}\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$.
--
--   The theorem restricts the search for an optimal robust assortment from all $2^n$ assortments to the collection $\widehat{\mathcal S}$, whose size depends on the structure of the past assortments; the algorithms and reformulations of the paper are built on it.
--
--   Differences from the source:
--   - encoding: standing assumption $\mathcal U\ne\emptyset$ stated once on p.8 → explicit hypothesis; reason: the paper assumes it throughout; same instances
--   - encoding: $\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$ → infimum of $\{\mathcal R^\lambda(S):\lambda\in\mathcal U\}$; reason: with $\mathcal U\ne\emptyset$ the set is nonempty, bounded below by 0 and its infimum is attained
--   - encoding: products $\{0,\dots,n\}$, rankings as bijections, past assortments $S_1,\dots,S_M$ → products $\mathrm{Fin}(n+1)$, rankings as permutations, past assortments indexed by $\mathrm{Fin}\,M$; reason: relabeling only
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Theorem 1, p.12

import Mathlib
import Definitions.Def_RankRobustAssort_IsOptimalRO
import Definitions.Def_RankRobustAssort_SHat

namespace RankRobustAssort

/-- **Theorem 1.** There exists an assortment `S ∈ Ŝ` that is optimal for `(RO)`:
for every problem instance (revenues `0 = r₀ < r₁ < ⋯ < r_n`, any past assortments
`S₁,…,S_M ⊆ 𝒩₀`, normalized sales data `v`, radius `η ≥ 0`, `ℓ₁` or `ℓ∞` norm) whose consistent
set `𝒰` is nonempty, some `S ∈ Ŝ` satisfies `min_{λ∈𝒰} ℛ^λ(S') ≤ min_{λ∈𝒰} ℛ^λ(S)` for every
`S' ∈ 𝒮`.

Sturt, arXiv:2112.05010v4, Theorem 1, p.12.

Formalization Note: `𝒰 ≠ ∅` is the paper's standing assumption (p.8), taken as the hypothesis
`hU`; without it `worstCase` would be the junk value `sInf ∅ = 0`. Optimality (`IsOptimalRO`) is
against all assortments containing `0`. -/
theorem exists_optimal_mem_SHat {n M : ℕ} (P : Problem n M) (hU : (consistentSet P).Nonempty) :
    ∃ S ∈ SHat P, IsOptimalRO P S := by sorry

end RankRobustAssort
