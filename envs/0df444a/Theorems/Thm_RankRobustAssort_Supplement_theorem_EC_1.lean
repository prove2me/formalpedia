-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_theorem_EC_1
-- name    : RankRobustAssort.Supplement.theorem_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:40:44.200815+00:00
-- url     : https://prove2.me/theorems/0e579a2e-a5af-581c-afb0-d2a4061d88da
-- title:
--   Theorem EC.1 — some assortment in $\widehat{\mathcal S}^{OO}$ is optimal for the optimistic problem (OO)
-- statement:
--   Consider any instance: revenues $0=r_0<r_1<\cdots<r_n$, past assortments $S_1,\dots,S_M\subseteq\mathcal N_0$, normalized sales data $v$, radius $\eta\ge0$, and the $\ell_1$- or $\ell_\infty$-norm, with nonempty consistent set $\mathcal U$. Let
--
--   $$
--   \widehat{\mathcal S}^{OO}=\{S\in\mathcal S:\ \text{if } i^*\in S,\ 0<r_i<r_{i^*},\text{ and }\mathcal M_{i^*}\subseteq\mathcal M_i,\text{ then } i\notin S\}.
--   $$
--
--   Then there exists an assortment $S\in\widehat{\mathcal S}^{OO}$ that is optimal for the optimistic optimization problem
--
--   $$
--   \text{(OO)}\qquad\max_{S\in\mathcal S}\ \max_{\lambda\in\mathcal U}\mathscr R^\lambda(S),
--   $$
--
--   that is, $\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S')\le\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S)$ for every $S'\in\mathcal S$.
--
--   This is the optimistic counterpart of Theorem 1: an optimal assortment for (OO) can be searched among assortments that contain no dominated product, which is what makes (OO) tractable for a fixed number of past assortments.
--
--   **Formalization Note.** $\mathcal U\neq\emptyset$ is the paper's standing assumption and is a hypothesis.
--
--   Differences from the source:
--   - encoding: $\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S)$ → the supremum of the values over $\mathcal U$; reason: under $\mathcal U\ne\emptyset$ the supremum is attained, so it is the paper's maximum
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Theorem EC.1 and the definition of Ŝ^OO, p.ec55; (OO), p.23

import Mathlib
import Definitions.Def_RankRobustAssort_Supplement_IsOptimalOO
import Definitions.Def_RankRobustAssort_Supplement_SHatOO

namespace RankRobustAssort.Supplement

/-- **Theorem EC.1.** There exists an assortment `S ∈ Ŝ^OO` that is optimal for `(OO)`:
for every problem instance (revenues `0 = r₀ < r₁ < ⋯ < r_n`, any past assortments
`S₁,…,S_M ⊆ 𝒩₀`, normalized sales data `v`, radius `η ≥ 0`, `ℓ₁` or `ℓ∞` norm) whose consistent
set `𝒰` is nonempty, some `S ∈ Ŝ^OO` satisfies `max_{λ∈𝒰} ℛ^λ(S') ≤ max_{λ∈𝒰} ℛ^λ(S)` for every
`S' ∈ 𝒮`.

Sturt, arXiv:2112.05010v4, Theorem EC.1, p.ec55; `Ŝ^OO`, p.ec55; (OO), p.23.

Formalization Note: `𝒰 ≠ ∅` is the paper's standing assumption (p.8), taken as the hypothesis
`hU`; without it `bestCase` would be the junk value `sSup ∅ = 0` and every assortment optimal.
Optimality (`IsOptimalOO`) is against all assortments containing `0`. -/
theorem theorem_EC_1 {n M : ℕ} (P : Problem n M) (hU : (consistentSet P).Nonempty) :
    ∃ S ∈ SHatOO P, IsOptimalOO P S := by sorry

end RankRobustAssort.Supplement
