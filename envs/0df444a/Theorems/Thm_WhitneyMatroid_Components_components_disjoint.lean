-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_components_disjoint
-- name    : WhitneyMatroid.Components.components_disjoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:49:57.709838+00:00
-- url     : https://prove2.me/theorems/7eb6b6da-e10f-4ffb-8b02-bc18cee761bb
-- title:
--   Theorem 14 — distinct components are disjoint
-- statement:
--   Let $M$ be a finite matroid. If $K_1$ and $K_2$ are components of $M$ (maximal nonempty non-separable subsets of the ground set) and $K_1\neq K_2$, then
--
--   $$
--   K_1\cap K_2=\emptyset .
--   $$
--
--   That is, no two distinct components of $M$ have common elements.
--
--   **Formalization Note** Components are those of the definition `IsComponent` (rank-defined, nonempty).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 519, Theorem 14

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_IsComponent

namespace WhitneyMatroid.Components

theorem components_disjoint {α : Type*} (M : Matroid α) [M.Finite]
    (K₁ K₂ : Set α) (hK₁ : IsComponent M K₁) (hK₂ : IsComponent M K₂) (hne : K₁ ≠ K₂) :
    Disjoint K₁ K₂ := by sorry

end WhitneyMatroid.Components
