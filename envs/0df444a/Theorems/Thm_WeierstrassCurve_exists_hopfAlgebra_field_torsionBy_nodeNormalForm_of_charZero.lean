-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/5162656d-d4b9-51e4-9e5c-af38fdd91574
-- title:
--   Hopf-algebra model for n-torsion of y²=x³+cx²
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be nonzero, and let $n$ be a natural number carrying a primality instance. Put $W : y^2 = x^3 + cx^2$, the Weierstrass curve over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,c,0,0,0)$, and let $\overline{K}$ be `AlgebraicClosure K` (equipped with decidable equality by classical choice). The assertion is that there exist a type $A$, a commutative ring structure on it, and a $K$-Hopf algebra structure on $A$ such that $A$ is finite as a $K$-module, its comultiplication is cocommutative, and there is a bijection $e_A$ from `WithConv (A →ₐ[K] AlgebraicClosure K)`, the set of $K$-algebra homomorphisms $A \to \overline{K}$ regarded as a monoid under convolution, onto the $n$-torsion submodule $\{P : nP = 0\}$ of the group $(W_{\overline{K}})$`.Point` of nonsingular affine points of $W$ over $\overline{K}$ together with the point at infinity, satisfying two compatibilities: $e_A(f \ast g) = e_A(f) + e_A(g)$ for all $f, g$; and for every $\sigma \in \mathrm{Aut}_K(\overline{K})$ and all $f, g$ with $g(a) = \sigma(f(a))$ for all $a \in A$, one has $e_A(g) = \sigma \cdot e_A(f)$.
--
--   For the nodal cubic $y^2 = x^3 + cx^2$ with $c \neq 0$ the group of nonsingular points over $\overline{K}$ is a one-dimensional torus, so its $n$-torsion is $\mu_n$; the statement packages that $n$-torsion, with its Galois action, as the points of a finite cocommutative $K$-Hopf algebra. It is the node-normal-form case used in the treatment of curves in characteristic zero that are not elliptic but have $c_4 \neq 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [Fact n.Prime] :
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
