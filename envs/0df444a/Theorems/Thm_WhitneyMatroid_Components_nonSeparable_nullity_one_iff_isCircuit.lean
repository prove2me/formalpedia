-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_nonSeparable_nullity_one_iff_isCircuit
-- name    : WhitneyMatroid.Components.nonSeparable_nullity_one_iff_isCircuit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:50.963833+00:00
-- url     : https://prove2.me/theorems/f0495fdd-2aa5-46af-a8fd-b5b305b72bd6
-- title:
--   Theorem 16 — non-separable of nullity 1 iff circuit
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$ with rank function $r$, and let $X\subseteq E$. Write $n(X)=\rho(X)-r(X)$ for the nullity of $X$ ($\rho(X)$ the number of its elements). Then
--
--   $$
--   X \text{ is non-separable and } n(X)=1 \iff X \text{ is a circuit of } M .
--   $$
--
--   Circuits (minimal dependent sets) are thus exactly the non-separable submatroids of the smallest possible positive nullity; they are the building blocks of non-separable matroids (Theorem 17).
--
--   **Formalization Note** Whitney states the theorem for a matroid $M$; here $X$ is a subset of the ground set of an ambient finite matroid, which is the same statement applied to the submatroid $X$ (a set is a circuit of the submatroid $X$ iff it is a circuit of $M$ contained in $X$). Circuits are Mathlib's `Matroid.IsCircuit`. A loop $\{e\}$ is a circuit, non-separable, and of nullity $1$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 519, Theorem 16

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_nullity

namespace WhitneyMatroid.Components

theorem nonSeparable_nullity_one_iff_isCircuit {α : Type*} (M : Matroid α) [M.Finite]
    (X : Set α) (hX : X ⊆ M.E) :
    (IsNonSeparable M X ∧ nullity M X = 1) ↔ M.IsCircuit X := by sorry

end WhitneyMatroid.Components
