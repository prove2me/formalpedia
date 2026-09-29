-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_padic_torsionBy_withConv_equiv_algClosure
-- name    : WeierstrassCurve.exists_hopfAlgebra_padic_torsionBy_withConv_equiv_algClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/c603e3d4-1688-5216-8d8b-2ff036b2d36c
-- title:
--   A finite cocommutative ℚₚ-Hopf algebra for V[p]
-- statement:
--   Let $p$ be a prime and let $V$ be a Weierstrass curve over $\mathbb{Q}_p$, with no further hypothesis on $V$ (in particular $V$ is not assumed to be elliptic). Fixing a decidable-equality structure on $\mathrm{AlgebraicClosure}\;\mathbb{Q}_p$ by classical choice, the assertion is that there exist a type $A$, a commutative ring structure on $A$ and a Hopf algebra structure on $A$ over $\mathbb{Q}_p$ such that: $A$ is finite as a $\mathbb{Q}_p$-module; its comultiplication is cocommutative; and there is a bijection $e_A$ from $\mathrm{WithConv}\,(A \to_{\mathrm{alg}[\mathbb{Q}_p]} \mathrm{AlgebraicClosure}\;\mathbb{Q}_p)$, the set of $\mathbb{Q}_p$-algebra homomorphisms from $A$ to a fixed algebraic closure of $\mathbb{Q}_p$ equipped with its convolution multiplication, onto the $p$-torsion submodule $\mathrm{torsionBy}\;\mathbb{Z}\;p$ of the group of affine points of the base change of $V$ to $\mathrm{AlgebraicClosure}\;\mathbb{Q}_p$, with two compatibilities: $e_A(f\cdot g) = e_A(f) + e_A(g)$ for all $f,g$, so that $e_A$ carries the convolution product to addition of points; and, for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\;\mathbb{Q}_p$ and all $f,g$ with $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_A(g) = \sigma \bullet e_A(f)$ for the Galois action on points.
--
--   This is the local, $\mathbb{Q}_p$-coefficient form of the statement that the $p$-torsion of a Weierstrass curve in characteristic $0$ is the group of geometric points of a finite cocommutative Hopf algebra, Galois-equivariantly: the coordinate ring of the kernel of multiplication by $p$, in its points formulation. It is used in the construction of finite flat prolongations of the $p$-torsion over $\mathbb{Z}_p$ when the discriminant is a unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_padic_torsionBy_withConv_equiv_algClosure.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_padic_torsionBy_withConv_equiv_algClosure
    (p : ℕ) [Fact p.Prime] (V : WeierstrassCurve ℚ_[p]) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra ℚ_[p] A),
      Module.Finite ℚ_[p] A ∧ Coalgebra.IsCocomm ℚ_[p] A ∧
      ∃ eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry
