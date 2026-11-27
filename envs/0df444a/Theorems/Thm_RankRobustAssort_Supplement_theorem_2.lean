-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_theorem_2
-- name    : RankRobustAssort.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:37:55.061607+00:00
-- url     : https://prove2.me/theorems/f2293409-0786-44ca-b3a9-45da7adffb6a
-- title:
--   Theorem 2 — for reverse revenue-ordered past assortments and $\eta=0$, every $\bar S\in\widehat{\mathcal S}$ is the unique robust optimum for some sales data
-- statement:
--   Suppose the past assortments are reverse revenue-ordered ($\mathcal M=\widetilde{\mathcal S}$: $S_1=\{0,n\}$, $S_m=\{0,\dots,m-1,n\}$, $m=2,\dots,n$), the radius is $\eta=0$, and the revenues $0=r_0<r_1<\cdots<r_n$ are fixed. Then for every assortment $\bar S\in\widehat{\mathcal S}$ there is a realization of the historical data $v=(v_{m,i}:m\in\mathcal M,\ i\in S_m)$ such that $\bar S$ is the unique optimal solution of the robust optimization problem
--
--   $$
--   \text{(RO)}\qquad\max_{S\in\mathcal S}\ \min_{\lambda\in\mathcal U}\mathscr R^\lambda(S).
--   $$
--
--   Precisely: there are valid sales data (nonnegative, summing to one on each $S_m$, zero on products not offered) whose consistent set $\mathcal U$ is nonempty, such that $\bar S$ is optimal for (RO) and every optimal solution of (RO) among all $S\in\mathcal S$ equals $\bar S$.
--
--   Together with Theorem 1, this shows that $\widehat{\mathcal S}$ is exactly the set of assortments that can be optimal for (RO) when the past assortments are reverse revenue-ordered, so its exponential size (Lemma 5) is not an artifact of the analysis.
--
--   **Formalization Note.** The revenues and the norm are taken from a given instance with these past assortments; the theorem produces a new instance with the same revenues, past assortments and norm, radius $0$, and new data.
--
--   Differences from the source:
--   - reading: $n$ products with $S_1=\{0,n\}$ and $\mathcal M=\{S_1,\dots,S_n\}$ (Definition 1) → $1\le n$; reason: Definition 1 needs $n$ to be a product; $n\ge1$ is its domain
--   - reading: "a realization of the historical data" → data satisfying the §2 conventions (values in $[0,1]$, summing to $1$ on each $S_m$, zero off $S_m$) whose consistent set $\mathcal U$ is nonempty; reason: the paper assumes throughout (p.8) that $\mathcal U\neq\emptyset$, so (RO) is defined only for such data; without it the worst case is not a minimum
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Theorem 2, p.14; Definition 1, p.14

import Mathlib
import Definitions.Def_RankRobustAssort_IsOptimalRO
import Definitions.Def_RankRobustAssort_SHat
import Definitions.Def_RankRobustAssort_Supplement_revPast

namespace RankRobustAssort.Supplement

/-- **Theorem 2.** Suppose that `ℳ = S̃`, that `η = 0`, and that the revenues `r₁ < ⋯ < r_n` are
fixed. Then for every assortment `S̄ ∈ Ŝ` there exists a realization of the historical data
`v ≡ (v_{m,i} : m ∈ ℳ, i ∈ S_m)` such that `S̄` is the unique optimal solution of `(RO)`.

Sturt, arXiv:2112.05010v4, Theorem 2, p.14; Definition 1, p.14.

Formalization Note: the instance `P` (with `P.S = revPast n`, i.e. `ℳ = S̃`) fixes the revenues
`P.r` and the norm; its own data, radius and norm play no further role, since `Ŝ` depends only on
the revenues and the past assortments. The conclusion produces a new instance `Q` with the same
revenues, the same past assortments, the same norm and `η = 0`, whose data `Q.v` is a valid
realization (the `Problem` fields: `0 ≤ v ≤ 1`, `∑_{i} v_{m,i} = 1`, `v_{m,i} = 0` for `i ∉ S_m`),
whose consistent set `𝒰` is nonempty (the paper's standing assumption, p.8, so that `(RO)` is in the
paper's setting and `worstCase` is a true minimum), for which `S̄` is optimal for `(RO)`, and for
which every optimal assortment of `(RO)` (optimality against all of `𝒮`) equals `S̄`.
`1 ≤ n` is the domain of Definition 1 (`S₁ = {0,n}` needs `n` to be a product). -/
theorem theorem_2 {n : ℕ} (hn : 1 ≤ n) (P : Problem n n) (hS : P.S = revPast n)
    (Sbar : Finset (Fin (n + 1))) (hSbar : Sbar ∈ SHat P) :
    ∃ Q : Problem n n, Q.r = P.r ∧ Q.S = P.S ∧ Q.η = 0 ∧ Q.norm = P.norm ∧
      (consistentSet Q).Nonempty ∧ IsOptimalRO Q Sbar ∧
      ∀ S : Finset (Fin (n + 1)), IsOptimalRO Q S → S = Sbar := by sorry

end RankRobustAssort.Supplement
