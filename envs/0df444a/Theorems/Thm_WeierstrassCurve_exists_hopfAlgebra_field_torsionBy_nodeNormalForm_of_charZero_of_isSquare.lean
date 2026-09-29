-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1f8ca1d0-5a2c-5969-9d04-58c8624380ed
-- title:
--   Hopf-algebra witness for n-torsion of a split node
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be non-zero, let $n$ be a prime, and suppose $c$ is a square, witnessed by $d \in K$ with $d \cdot d = c$. Let $W$ be the Weierstrass curve over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,c,0,0,0)$, that is $y^2 = x^3 + c x^2$. The assertion is that there exists a type $A$, carrying a commutative ring structure and a $K$-Hopf-algebra structure, such that $A$ is finite as a $K$-module, its comultiplication is cocommutative, and there is a bijection $e_A$ from the type of $K$-algebra homomorphisms $A \to \overline{K}$ (where $\overline{K} =$ `AlgebraicClosure K`), equipped with the convolution product coming from the Hopf structure, onto the $n$-torsion submodule $\{P : nP = 0\}$ of the $\mathbb{Z}$-module of points of $W$ over $\overline{K}$, with the two properties: $e_A(f \cdot g) = e_A(f) + e_A(g)$ for all $f, g$, so that $e_A$ turns the convolution product into addition of points; and, for every $K$-algebra automorphism $\sigma$ of $\overline{K}$ and all $f, g$ with $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_A(g) = \sigma \cdot e_A(f)$, the action being the Galois action on torsion points. Primality of $n$ enters only through $n \neq 0$.
--
--   This is the split-node case of the description of the $n$-torsion of a Weierstrass curve in node normal form: when the tangent directions $y = \pm d x$ at the node are $K$-rational, the non-singular part is $\overline{K}^{\times}$ Galois-equivariantly, so the $n$-torsion is $\mu_n$ and is represented by the group scheme $\operatorname{Spec} K[\mathbb{Z}/n\mathbb{Z}]$. It feeds the statement [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero), which removes the hypothesis that $c$ be a square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [Fact n.Prime]
    (d : K) (hd : d * d = c) :
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
