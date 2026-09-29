-- Prove2me | Theorems.Thm_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top
-- name    : Representation.isAbsolutelyIrreducible_matrix_iff_span_range_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/2551f662-0736-5232-ba82-8527f59a5420
-- title:
--   Burnside's criterion for absolute irreducibility
-- statement:
--   Let $n$ be a finite nonempty index type, let $G$ be a group and $k$ a field, both of types in a fixed universe $u$, and let $\varphi : G \to \mathrm{GL}_n(k)$ be a group homomorphism into the general linear group of $n\times n$ invertible matrices over $k$. Write $\rho_\varphi$ for the associated linear representation of $G$ on $n \to k$, namely [`Deformation.matrixRepresentation φ`](def/Deformations_MatrixRepresentation.html#L15), obtained by composing $\varphi$ with the monoid map sending an invertible matrix to the linear automorphism it induces and then with the coercion of units into endomorphisms. The theorem asserts the equivalence of two statements. The first is that $\rho_\varphi$ satisfies [`Representation.IsAbsolutelyIrreducible`](def/Representation_AbsolutelyIrreducible.html#L27) in universe $u$: for every type $k'$ in universe $u$ equipped with a field structure and with a $k$-algebra structure, the base-changed representation $k' \otimes_k \rho_\varphi$ is irreducible. The second is the Burnside spanning condition that the $k$-submodule of $n \times n$ matrices spanned by the set of underlying matrices $\{(\varphi g)^{\flat} : g \in G\}$ is the whole matrix space, i.e. equals $\top$. No hypothesis is placed on $k$ beyond being a field, and $G$ is an arbitrary abstract group, with no topology or continuity involved.
--
--   This is Burnside's classical characterisation of absolute irreducibility of a matrix representation by the condition that its image spans the full matrix algebra, here in the form of a biconditional over an arbitrary field. It serves as the dictionary between the intrinsic absolute-irreducibility predicate and the spanning condition used in commutant and trace arguments, and is cited by [`ResidualGaloisRep.isAbsolutelyIrreducible_iff_matrixRepresentation`](thm.html#ResidualGaloisRep.isAbsolutelyIrreducible_iff_matrixRepresentation) for residual Galois representations; the forward implication is supplied by [`Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix`](thm.html#Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top.lean

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Representation.isAbsolutelyIrreducible_matrix_iff_span_range_eq_top {n : Type} [Fintype n] [DecidableEq n] {G : Type u}
    [Group G] {k : Type u} [Field k] [Nonempty n] (φ : G →* GL n k) :
    Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation φ) ↔
      Submodule.span k (Set.range fun g => (φ g).val) = ⊤ := by sorry
