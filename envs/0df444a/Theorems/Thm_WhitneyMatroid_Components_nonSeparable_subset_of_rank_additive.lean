-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_nonSeparable_subset_of_rank_additive
-- name    : WhitneyMatroid.Components.nonSeparable_subset_of_rank_additive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:00.139987+00:00
-- url     : https://prove2.me/theorems/efac12cd-d032-45b8-8b1d-403d72aac9c7
-- title:
--   Theorem 12 — a non-separable set lies inside one part of a rank-additive union
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$ with rank function $r$, and let $M_1, M_2\subseteq E$ satisfy
--
--   $$
--   r(M_1 + M_2) = r(M_1) + r(M_2).
--   $$
--
--   If $M'\subseteq M_1 + M_2$ is non-separable, then either $M'\subseteq M_1$ or $M'\subseteq M_2$.
--
--   Thus a rank-additive division of a matroid cannot cut through a non-separable part; this is the step from rank additivity to the structure of components.
--
--   **Formalization Note** As in Theorem 11, $M_1$ and $M_2$ are subsets of the ground set of an ambient finite matroid (Whitney's matroid $M = M_1+M_2$ is the corresponding submatroid), and they are not required to be disjoint. Non-separability is the notion of §10 (division into two nonempty disjoint groups with additive rank).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 519, Theorem 12

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable

namespace WhitneyMatroid.Components

theorem nonSeparable_subset_of_rank_additive {α : Type*} (M : Matroid α) [M.Finite]
    (M₁ M₂ N : Set α) (hM₁ : M₁ ⊆ M.E) (hM₂ : M₂ ⊆ M.E)
    (hr : M.eRk (M₁ ∪ M₂) = M.eRk M₁ + M.eRk M₂)
    (hN : IsNonSeparable M N) (hNsub : N ⊆ M₁ ∪ M₂) :
    N ⊆ M₁ ∨ N ⊆ M₂ := by sorry

end WhitneyMatroid.Components
