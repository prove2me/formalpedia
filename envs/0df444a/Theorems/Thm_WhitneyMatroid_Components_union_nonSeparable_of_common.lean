-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_union_nonSeparable_of_common
-- name    : WhitneyMatroid.Components.union_nonSeparable_of_common
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:51.622098+00:00
-- url     : https://prove2.me/theorems/7a4b5280-b893-445b-a103-9800796babd6
-- title:
--   Theorem 13 — two non-separable sets with a common element have a non-separable union
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$, and let $M_1, M_2\subseteq E$ be non-separable submatroids having a common element $e$. Then their union
--
--   $$
--   M_1 + M_2
--   $$
--
--   is non-separable.
--
--   This is the gluing property that makes the maximal non-separable parts (components) of a matroid pairwise disjoint (Theorem 14).
--
--   **Formalization Note** $M_1$ and $M_2$ are subsets of the ground set of a fixed finite matroid, as in Whitney's proof; $+$ is set union.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 519, Theorem 13

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable

namespace WhitneyMatroid.Components

theorem union_nonSeparable_of_common {α : Type*} (M : Matroid α) [M.Finite]
    (M₁ M₂ : Set α) (e : α) (h₁ : IsNonSeparable M M₁) (h₂ : IsNonSeparable M M₂)
    (he₁ : e ∈ M₁) (he₂ : e ∈ M₂) :
    IsNonSeparable M (M₁ ∪ M₂) := by sorry

end WhitneyMatroid.Components
