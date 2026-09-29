-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1d710447-db79-50ac-9003-9b164649077c
-- title:
--   Nodal Weierstrass curves: n-torsion as points of a finite Hopf algebra
-- statement:
--   Let $K$ be a field of characteristic zero, let $W$ be a Weierstrass curve over $K$ which is not elliptic (its discriminant is not a unit) and whose invariant $c_4$ is nonzero, and let $n$ be a natural number assumed prime. Then there exist a type $A$ carrying a commutative ring structure and a $K$-Hopf algebra structure such that $A$ is finite as a $K$-module and its coalgebra structure is cocommutative, together with a bijection $e_A$ from the type $\mathrm{WithConv}(A \to_{\mathrm{alg}[K]} \overline K)$ of $K$-algebra homomorphisms $A \to \overline K$, equipped with its convolution multiplication, onto the $\mathbb Z$-torsion submodule killed by $n$ of the group of (nonsingular) points of the base change of $W$ to $\overline K$, where $\overline K$ is `AlgebraicClosure K`; the bijection satisfies $e_A(fg) = e_A f + e_A g$ for all $f, g$, and is Galois-equivariant in the form: for every $K$-algebra automorphism $\sigma$ of $\overline K$ and all $f, g$, if $g(a) = \sigma(f(a))$ for every $a \in A$, then $e_A g = \sigma \cdot e_A f$. Thus $W[n](\overline K)$ is realised, as a Galois module, by the $\overline K$-points of a finite cocommutative $K$-Hopf algebra.
--
--   This is the nodal case ($c_4 \neq 0$) of the statement that, for a singular Weierstrass curve in characteristic zero, the $n$-torsion of the group of nonsingular points over the algebraic closure is the Galois module of points of a finite flat group scheme over $K$; over $\overline K$ the smooth locus of a nodal curve is $\mathbb G_m$, which is split over $K$ only up to a quadratic twist. It is combined with the cuspidal case to give [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (hc4 : W.c₄ ≠ 0) (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry
