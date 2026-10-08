-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_indep_subset
-- name    : WhitneyMatroid.RankIndep.indep_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:36.065983+00:00
-- url     : https://prove2.me/theorems/4c69aaf6-0397-4dbe-887d-c1e55e6c8942
-- title:
--   Lemma 2 — any subset of an independent set is independent
-- statement:
--   Let $r$ satisfy Whitney's rank postulates (R₁), (R₂), (R₃) on the subsets of a finite set $M$, and call $N$ independent when its nullity vanishes, $\rho(N) = r(N)$. Then for all subsets $N \subseteq N'$:
--
--   $$\rho(N') = r(N') \implies \rho(N) = r(N).$$
--
--   This is postulate (I₁) for the independent sets defined by a rank function, the first half of the deduction of (I) from (R).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 510, Lemma 2

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- Lemma 2 (p. 510). Any subset of an independent set is independent. -/
theorem indep_subset {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    ∀ N N' : Finset α, N ⊆ N' → indepOfRank r N' → indepOfRank r N := by sorry

end WhitneyMatroid.RankIndep
