-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_component_decomposition_unique
-- name    : WhitneyMatroid.Components.component_decomposition_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:50:34.072651+00:00
-- url     : https://prove2.me/theorems/0d01eb4e-bf5c-494e-9226-880b16c75cf9
-- title:
--   Theorem 15 — a matroid is the sum of its components in a unique manner
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$, and let $\mathcal C(M)$ be the set of its components. Then
--
--   1. the components cover the ground set:
--   $$
--   \bigcup_{K\in\mathcal C(M)} K = E;
--   $$
--   2. the expression is unique: if $\mathcal K$ is any family of components of $M$ whose union is $E$, then $\mathcal K = \mathcal C(M)$.
--
--   Together with Theorem 14 (distinct components are disjoint), this says that every matroid is, in exactly one way, the sum of disjoint components.
--
--   **Formalization Note** "Expressed as a sum of components" is read as "the union of a family of components equals the ground set", and "in a unique manner" as "that family is necessarily the family of all components". For the matroid with no elements both families are empty, which is why components are required to be nonempty.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 519, Theorem 15

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_IsComponent

namespace WhitneyMatroid.Components

theorem component_decomposition_unique {α : Type*} (M : Matroid α) [M.Finite] :
    ⋃₀ {K : Set α | IsComponent M K} = M.E ∧
    ∀ 𝒦 : Set (Set α), (∀ K ∈ 𝒦, IsComponent M K) → ⋃₀ 𝒦 = M.E →
      𝒦 = {K : Set α | IsComponent M K} := by sorry

end WhitneyMatroid.Components
