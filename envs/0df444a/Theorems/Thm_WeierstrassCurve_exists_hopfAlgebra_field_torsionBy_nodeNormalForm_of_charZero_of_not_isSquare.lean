-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/0039eede-c3b1-5475-ae21-d353146c8b8e
-- title:
--   Twisted μₙ Hopf algebra for a non-split node
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be nonzero and not a square in $K$, and let $n$ be a natural number that is prime. Put $W : y^2 = x^3 + c x^2$, the Weierstrass curve over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,c,0,0,0)$. The assertion is that there exist a type $A$ carrying a commutative ring structure and a $K$-Hopf-algebra structure such that $A$ is a finite $K$-module and is cocommutative as a $K$-coalgebra, together with a bijection $e_A$ from `WithConv (A →ₐ[K] AlgebraicClosure K)`, the set of $K$-algebra homomorphisms $A \to \overline{K}$ with its multiplicative (convolution) structure, onto the $n$-torsion submodule `Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n` of the group of nonsingular points of $W$ over $\overline{K}$, subject to two compatibilities: $e_A(fg) = e_A f + e_A g$ for all $f, g$, so that $e_A$ is a monoid-to-group isomorphism; and, for every $K$-algebra automorphism $\sigma$ of $\overline{K}$ and all $f, g$ with $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_A g = \sigma \bullet e_A f$, i.e. $e_A$ is equivariant for the Galois action on homomorphisms into $\overline{K}$ and on torsion points.
--
--   This is the non-split case of the construction of a finite cocommutative Hopf algebra over $K$ whose $\overline{K}$-points, with their Galois action, realise the $n$-torsion of a node normal form; here the relevant group scheme is the quadratic twist of $\mu_n$ by $K(\sqrt{c})/K$. It feeds the combined node statement [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero), which supplies such group-scheme models of torsion in the finite-flat part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [Fact n.Prime]
    (hnsq : ¬ IsSquare c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry
