-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_rank_submodular
-- name    : WhitneyMatroid.RankIndep.rank_submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:57.361271+00:00
-- url     : https://prove2.me/theorems/2455d9e4-7d0e-43e2-b519-15ccc68906f2
-- title:
--   Theorem 3 — submodularity of rank, (3.2) and (3.3)
-- statement:
--   Let $r$ satisfy Whitney's rank postulates (R₁), (R₂), (R₃) on the subsets of a finite set, and let $\Delta(M, N) = r(M + N) - r(M)$ as in (3.1), with $+$ denoting union and $M_1 M_2$ intersection. Then
--
--   1. for all subsets $M, N_1, N_2$: $\Delta(M + N_2, N_1) \le \Delta(M, N_1)$;
--   2. equivalently, (3.2): for all subsets $M, N_1, N_2$,
--   $$r(M + N_1 + N_2) \le r(M + N_1) + r(M + N_2) - r(M);$$
--   3. equivalently, (3.3): for all subsets $M_1, M_2$,
--   $$r(M_1 + M_2) \le r(M_1) + r(M_2) - r(M_1 M_2).$$
--
--   This is the submodular inequality for the rank function, derived here from the local postulates (R₁)–(R₃) alone. It is the central property of rank in Whitney's paper.
--
--   **Formalization Note** The paper states the first two forms as alternatives ("or") and calls (3.3) evidently equivalent; all three are asserted, as a conjunction. $M$, $N_1$, $N_2$, $M_1$, $M_2$ are arbitrary subsets, not only the whole matroid.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 511, Theorem 3, (3.2), (3.3)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- Theorem 3 (p. 511). `Δ(M + N₂, N₁) ≤ Δ(M, N₁)`, or, (3.2)
`r(M + N₁ + N₂) ≤ r(M + N₁) + r(M + N₂) − r(M)`; and the equivalent form (3.3)
`r(M₁ + M₂) ≤ r(M₁) + r(M₂) − r(M₁M₂)`. Here `+` is union and `M₁M₂` intersection. -/
theorem rank_submodular {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    (∀ M N₁ N₂ : Finset α, Delta r (M ∪ N₂) N₁ ≤ Delta r M N₁) ∧
    (∀ M N₁ N₂ : Finset α, r (M ∪ N₁ ∪ N₂) ≤ r (M ∪ N₁) + r (M ∪ N₂) - r M) ∧
    (∀ M₁ M₂ : Finset α, r (M₁ ∪ M₂) ≤ r M₁ + r M₂ - r (M₁ ∩ M₂)) := by sorry

end WhitneyMatroid.RankIndep
