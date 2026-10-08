-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_delta_union_le
-- name    : WhitneyMatroid.RankIndep.delta_union_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:47.150092+00:00
-- url     : https://prove2.me/theorems/ed996eae-27e4-4f40-b0ea-2c4e99c3e5b2
-- title:
--   Lemma 4 — $\Delta(M + N, e) \le \Delta(M, e)$
-- statement:
--   Let $r$ satisfy Whitney's rank postulates (R₁), (R₂), (R₃) on the subsets of a finite set, and let $\Delta(M, N) = r(M + N) - r(M)$ as in (3.1), with $+$ denoting union. For all subsets $M, N$ and every element $e$,
--
--   $$\Delta(M + N, e) \le \Delta(M, e).$$
--
--   Adding any set $N$ beforehand can only decrease the rank gained by adding a single element $e$. Lemma 4 is the step from Lemma 3 to the submodularity of rank (Theorem 3) and is used again in the deduction of (I₂) in §4.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 511, Lemma 4

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- Lemma 4 (p. 511). `Δ(M + N, e) ≤ Δ(M, e)`, for any subsets `M, N` and element `e`. -/
theorem delta_union_le {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    ∀ (M N : Finset α) (e : α), Delta r (M ∪ N) {e} ≤ Delta r M {e} := by sorry

end WhitneyMatroid.RankIndep
