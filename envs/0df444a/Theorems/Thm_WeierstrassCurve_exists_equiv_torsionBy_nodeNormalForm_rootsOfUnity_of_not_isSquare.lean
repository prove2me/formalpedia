-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
-- name    : WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/954b6379-2b7a-5471-a90c-67510427b746
-- title:
--   n-torsion of a non-split nodal cubic is twisted μₙ
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be non-zero, let $n$ be a positive natural number, and assume $c$ is not a square in $K$. Put $W : y^2 = x^3 + c\,x^2$, the Weierstrass curve over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,c,0,0,0)$. The assertion is that there exist an element $\delta$ of the algebraic closure $\overline K$ with $\delta^2$ equal to the image of $c$, and a bijection $e_t$ from the $n$-torsion submodule of the group of points of the base change of $W$ to $\overline K$ (the points being the point at infinity together with the nonsingular affine points) onto the group $\mu_n(\overline K)$ of $n$-th roots of unity in $\overline K^\times$, such that: $e_t(P+Q) = e_t(P)\,e_t(Q)$ for all $n$-torsion points $P,Q$; and for every $K$-algebra automorphism $\sigma$ of $\overline K$ and every $n$-torsion point $P$, if $\sigma\delta = \delta$ then $e_t(\sigma \cdot P) = \sigma(e_t(P))$ in $\overline K$, while if $\sigma\delta = -\delta$ then $e_t(\sigma \cdot P)\cdot \sigma(e_t(P)) = 1$.
--
--   This is the non-split case of the description of the group of nonsingular points of a nodal cubic: over $\overline K$ the parametrisation $(x,y) \mapsto (y-\delta x)/(y+\delta x)$ identifies the points with $\overline K^\times$, and on $n$-torsion it gives $\mu_n$ twisted by the quadratic character of $K(\delta)/K$, so that the torsion is that of the norm-one torus of the quadratic extension. It feeds the construction of the corresponding Hopf-algebra witness in [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare), and the proof cites [`WeierstrassCurve.Affine.Point.exists_addEquiv_nodeNormalForm_additive_units`](thm.html#WeierstrassCurve.Affine.Point.exists_addEquiv_nodeNormalForm_additive_units) for the underlying group isomorphism onto the units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [NeZero n]
    (hnsq : ¬ IsSquare c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ (δ : AlgebraicClosure K), δ * δ = algebraMap K (AlgebraicClosure K) c ∧
      ∃ et : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n
          ≃ rootsOfUnity n (AlgebraicClosure K),
        (∀ P Q, et (P + Q) = et P * et Q) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (P : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n),
          (σ δ = δ →
            ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            = σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∧
          (σ δ = -δ →
            ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            * σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by sorry
