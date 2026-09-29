-- Prove2me | Theorems.Thm_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two
-- name    : Representation.finrank_invariants_eq_one_of_natCard_map_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7d0c7980-35ec-561a-93ba-0f476000ac23
-- title:
--   Non-central order-two image in GL₂ fixes a line
-- statement:
--   Let $\Gamma$ be a group, $k$ a field, $\rho\colon\Gamma\to \mathrm{GL}_2(k)$ a group homomorphism (into the general linear group of $2\times 2$ matrices indexed by `Fin 2`), and let $I\le\Gamma$ be a subgroup. Assume the image subgroup $\rho(I)\le \mathrm{GL}_2(k)$ has exactly two elements, and that $\rho(I)$ is not contained in the centre of $\mathrm{GL}_2(k)$. Write [`Deformation.matrixRepresentation`](def/Deformations_MatrixRepresentation.html#L15) $\rho$ for the $k$-linear representation of $\Gamma$ on $k^2$ obtained by composing $\rho$ with the passage from an invertible matrix to the associated linear automorphism of `Fin 2 → k` and then to its underlying $k$-linear endomorphism; restrict it along the inclusion of $I$ into $\Gamma$. The conclusion is that the invariant submodule of this restricted representation, that is the set of $v\in k^2$ with $\rho(\sigma)\,v=v$ for all $\sigma\in I$, is a $k$-subspace of dimension exactly $1$.
--
--   This is the linear-algebra input to the computation of the tame part of the Artin conductor of a two-dimensional representation at a place whose inertia acts through a group of order two: there $\dim V-\dim V^{I}=2-1=1$, so the place divides the conductor exactly once. It is cited in the construction, via Langlands–Tunnell, of a weight-one form whose level is exactly divisible by $3$ for a mod-$3$ representation with inertia image of order two at $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two.lean

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

universe u

theorem Representation.finrank_invariants_eq_one_of_natCard_map_eq_two
    {Γ : Type u} [Group Γ] {k : Type u} [Field k]
    (ρ : Γ →* GL (Fin 2) k) (I : Subgroup Γ)
    (hcard : Nat.card (I.map ρ) = 2)
    (hcent : ¬ I.map ρ ≤ Subgroup.center (GL (Fin 2) k)) :
    Module.finrank k
        (Representation.invariants
          ((Deformation.matrixRepresentation ρ).comp I.subtype)) = 1 := by sorry
