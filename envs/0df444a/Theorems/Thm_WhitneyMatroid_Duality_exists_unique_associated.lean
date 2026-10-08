-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_exists_unique_associated
-- name    : WhitneyMatroid.Duality.exists_unique_associated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:44:39.533972+00:00
-- url     : https://prove2.me/theorems/6965fb78-2191-4b9c-8a2b-5ea5a1826dd6
-- title:
--   Theorem 27 — a subspace of $E_n$ has a unique associated matroid
-- statement:
--   Let $H$ be a hyperplane through the origin (a linear subspace) of $n$-dimensional Euclidean space $E_n$. For a set $S$ of coordinates let $r_H(S)$ be the dimension of the projection of $H$ onto the coordinate subspace of the coordinates in $S$. Then there is exactly one matroid $M$ on the elements $e_1,\dots,e_n$ (one per coordinate) whose rank function is $r_H$:
--
--   $$
--   \exists!\, M\quad\text{such that}\quad r_M(\{e_i : i\in S\}) = r_H(S)\ \text{ for all } S\subseteq\{1,\dots,n\}.
--   $$
--
--   This is what makes "the matroid associated with $H$" well defined; it is the matroid in Theorem 28.
--
--   **Formalization Note** Matroids are Mathlib `Matroid (Fin n)` with ground set all of `Fin n`; the rank condition is the predicate `IsAssociated` (rank `eRk` equal to the `finrank` of the coordinate projection of $H$). Uniqueness is among all such matroids.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 526, Theorem 27

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsAssociated

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 27 (p. 526): there is a unique matroid `M` associated with any hyperplane `H`
through the origin in `Eₙ`, i.e. a unique matroid on the coordinates `e₁, …, eₙ` in which every
subset has as rank the dimension of the projection of `H` onto the corresponding coordinate
subspace. -/
theorem exists_unique_associated (n : ℕ) (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃! M : Matroid (Fin n), IsAssociated M H := by sorry

end WhitneyMatroid.Duality
