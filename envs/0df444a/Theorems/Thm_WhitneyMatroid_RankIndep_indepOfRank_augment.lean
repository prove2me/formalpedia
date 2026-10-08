-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_indepOfRank_augment
-- name    : WhitneyMatroid.RankIndep.indepOfRank_augment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:53.836688+00:00
-- url     : https://prove2.me/theorems/1c4fea2e-7070-44f2-922f-0c60cc98deca
-- title:
--   §4 — the independent sets of a rank system satisfy (I₂)
-- statement:
--   Let $r$ satisfy Whitney's rank postulates (R₁), (R₂), (R₃) on the subsets of a finite set, and call $N$ independent when $\rho(N) = r(N)$, $\rho$ counting elements. Then the independent sets satisfy postulate (I₂): if $N$ and $N'$ are independent and $N'$ has exactly one element more than $N$,
--
--   $$\rho(N') = \rho(N) + 1,$$
--
--   then there is an element $e' \in N'$ with $e' \notin N$ such that $N + e'$ is independent.
--
--   Together with Lemma 2, this deduces the independence postulates (I) from the rank postulates (R), one half of Whitney's equivalence theorem.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 511–512, §4 (deduction of (I₂) from (R₁), (R₂), (R₃))

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- §4 (pp. 511–512). Under (R₁), (R₂), (R₃), the independent sets `n(N) = 0` satisfy (I₂). -/
theorem indepOfRank_augment {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    IndepI2 (indepOfRank r) := by sorry

end WhitneyMatroid.RankIndep
