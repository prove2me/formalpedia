-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_exists_subset_union_isBase
-- name    : WhitneyMatroid.Duality.exists_subset_union_isBase
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:43:33.279832+00:00
-- url     : https://prove2.me/theorems/71d77e69-e312-486e-906f-8abf67b9a527
-- title:
--   Theorem 8 — an independent set extends to a base by elements of a given base
-- statement:
--   Let $M$ be a matroid on a finite set of elements. If $B$ is a base of $M$ and $N$ is an independent set, then there is a subset $N'$ of $B$ such that
--
--   $$
--   N \cup N' \ \text{ is a base of } M.
--   $$
--
--   Any independent set can thus be completed to a base using only elements of a prescribed base. Whitney uses it in the proof of Theorem 23 to find a base of $M'$ with the maximal number of elements inside a given set.
--
--   **Formalization Note** The matroid is a Mathlib `Matroid` on a finite type with ground set the whole type; Whitney's $N+N'$ is the union $N\cup N'$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 515, Theorem 8

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 8 (p. 515): in a matroid `M` on a finite set of elements, if `B` is a base
and `N` is independent, then for some subset `N′` of `B`, `N + N′` is a base. -/
theorem exists_subset_union_isBase {α : Type*} [Finite α] (M : Matroid α)
    (hE : M.E = Set.univ) {B N : Set α} (hB : M.IsBase B) (hN : M.Indep N) :
    ∃ N' : Set α, N' ⊆ B ∧ M.IsBase (N ∪ N') := by sorry

end WhitneyMatroid.Duality
