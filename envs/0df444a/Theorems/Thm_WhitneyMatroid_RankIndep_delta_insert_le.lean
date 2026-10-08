-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_delta_insert_le
-- name    : WhitneyMatroid.RankIndep.delta_insert_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:43.794729+00:00
-- url     : https://prove2.me/theorems/9e5c1297-be57-4b70-989b-823b2683c88a
-- title:
--   Lemma 3 — $\Delta(M + e_2, e_1) \le \Delta(M, e_1)$
-- statement:
--   Let $r$ satisfy Whitney's rank postulates (R₁), (R₂), (R₃) on the subsets of a finite set, and let $\Delta(M, N) = r(M + N) - r(M)$ as in (3.1), with $+$ denoting union. For every subset $M$ and all elements $e_1, e_2$,
--
--   $$\Delta(M + e_2, e_1) \le \Delta(M, e_1).$$
--
--   The gain in rank from adding $e_1$ does not increase when $e_2$ is added first. This is the one-element case of Lemma 4 and of the submodularity inequality, Theorem 3.
--
--   **Formalization Note** No hypothesis on $e_1, e_2$ is imposed: the paper does not restrict them, and when $e_1$ or $e_2$ already lies in $M$, or $e_1 = e_2$, the inequality still holds as stated. $\Delta(M, e)$ is $\Delta(M, \{e\})$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 511, Lemma 3

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- Lemma 3 (p. 511). `Δ(M + e₂, e₁) ≤ Δ(M, e₁)`, for any subset `M` and elements `e₁, e₂`. -/
theorem delta_insert_le {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    ∀ (M : Finset α) (e₁ e₂ : α), Delta r (insert e₂ M) {e₁} ≤ Delta r M {e₁} := by sorry

end WhitneyMatroid.RankIndep
