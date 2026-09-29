-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/3872ab9c-73ab-56cb-bd47-79e91e0a3dbc
-- title:
--   Cuspidal Weierstrass curves: n-torsion as Hopf algebra points
-- statement:
--   Let $K$ be a field of characteristic zero, let $W$ be a Weierstrass curve over $K$ which is not elliptic (its discriminant is not a unit), assume $c_4(W)=0$, and let $n$ be a prime natural number. Then there exist a type $A$ carrying a commutative ring structure and a Hopf algebra structure over $K$ such that $A$ is finite as a $K$-module and its comultiplication is cocommutative, together with a bijection $e_A$ from $\mathrm{WithConv}(A \to_{\mathrm{alg}[K]} \overline{K})$, the set of $K$-algebra homomorphisms $A \to \overline{K}$ equipped with its convolution monoid structure, onto the $\mathbb{Z}$-torsion submodule $\{P : nP = 0\}$ of the group $W(\overline{K})$ of affine nonsingular points of the base change of $W$ to an algebraic closure $\overline{K}$, subject to two compatibilities: $e_A(f\cdot g) = e_A(f) + e_A(g)$ for all $f,g$, so that $e_A$ is an isomorphism of the convolution monoid onto the $n$-torsion group; and for every $K$-algebra automorphism $\sigma$ of $\overline{K}$ and all $f,g$ with $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_A(g) = \sigma \bullet e_A(f)$, i.e. $e_A$ is Galois-equivariant.
--
--   This is the cuspidal case ($c_4 = 0$) of the statement that the $n$-torsion of the smooth locus of a Weierstrass curve is represented by a finite cocommutative Hopf algebra over the base field, with its Galois action; here the smooth locus is a form of $\mathbb{G}_a$ and so, in characteristic zero, has no nontrivial torsion. It feeds into [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero), which combines it with the nodal case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (hc4 : W.c₄ = 0) (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry
