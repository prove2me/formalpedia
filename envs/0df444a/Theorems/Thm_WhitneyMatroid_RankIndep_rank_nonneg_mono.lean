-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_rank_nonneg_mono
-- name    : WhitneyMatroid.RankIndep.rank_nonneg_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:27.770481+00:00
-- url     : https://prove2.me/theorems/905185ab-d7b8-416d-a2d1-44bb48c9d8a4
-- title:
--   Lemma 1 — rank and nullity are nonnegative and monotone
-- statement:
--   Let $r$ be a rank function on the subsets of a finite set $M$ satisfying Whitney's postulates (R₁), (R₂), (R₃), and let $n(N) = \rho(N) - r(N)$ be the nullity, where $\rho(N)$ is the number of elements of $N$. Then for every subset $N$,
--
--   $$r(N) \ge 0 \quad\text{and}\quad n(N) \ge 0,$$
--
--   and for all subsets $N \subseteq M'$,
--
--   $$r(N) \le r(M') \quad\text{and}\quad n(N) \le n(M').$$
--
--   So the rank never exceeds the number of elements, and enlarging a set never decreases its rank or its nullity. These are the basic inequalities used throughout Whitney's paper.
--
--   **Formalization Note** Whitney states the monotonicity for $N \subset M$ with $M$ the whole matroid; since every subset of a matroid is a matroid, the statement is formalized for an arbitrary pair $N \subseteq M'$, the form in which it is used later. The symbol $\subset$ in the paper denotes inclusion, not proper inclusion.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 510, Lemma 1

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- Lemma 1 (p. 510). For any `N`, `r(N) ≥ 0` and `n(N) ≥ 0`. If `N ⊆ M`, then
`r(N) ≤ r(M)` and `n(N) ≤ n(M)`. -/
theorem rank_nonneg_mono {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    (∀ N : Finset α, 0 ≤ r N ∧ 0 ≤ nullity r N) ∧
    (∀ N M : Finset α, N ⊆ M → r N ≤ r M ∧ nullity r N ≤ nullity r M) := by sorry

end WhitneyMatroid.RankIndep
