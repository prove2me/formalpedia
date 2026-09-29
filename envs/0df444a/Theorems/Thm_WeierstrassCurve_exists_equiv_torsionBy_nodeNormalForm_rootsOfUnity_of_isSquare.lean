-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
-- name    : WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/b4a14b88-8654-569b-816b-1b0caa828dfd
-- title:
--   Split-node n-torsion is μₙ, Galois-equivariantly
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be non-zero, let $n$ be a non-zero natural number, and let $d \in K$ satisfy $d \cdot d = c$. Let $W$ be the Weierstrass curve over $K$ with coefficients $a_1 = 0$, $a_2 = c$, $a_3 = 0$, $a_4 = 0$, $a_6 = 0$, that is $y^2 = x^3 + c x^2$, a curve with a split node at the origin. Write $\overline{K}$ for `AlgebraicClosure K` and consider the group of affine points of the base change of $W$ to $\overline{K}$ (points $(x,y)$ on the curve at which it is nonsingular, together with the point at infinity). The assertion is that there is a bijection $et$ between the $\mathbb{Z}$-submodule of those points $P$ with $(n : \mathbb{Z}) \cdot P = 0$ and the group $\mu_n(\overline{K})$ of $n$-th roots of unity in $\overline{K}^{\times}$, such that, first, $et(P + Q) = et(P) \cdot et(Q)$ for all $P, Q$, so that $et$ is an isomorphism of groups (stated as a type equivalence together with this multiplicativity, rather than as a bundled multiplicative equivalence), and second, for every $K$-algebra automorphism $\sigma$ of $\overline{K}$ and every such $P$, the element of $\overline{K}$ underlying $et(\sigma \cdot P)$ equals $\sigma$ applied to the element underlying $et(P)$; here $\sigma \cdot P$ is the action of $\sigma$ on points by coordinatewise application.
--
--   This is the $n$-torsion part of the classical identification of the group of nonsingular points of a split nodal cubic over an algebraically closed field with the multiplicative group, via $(x,y) \mapsto (y - dx)/(y + dx)$, here recorded with its Galois equivariance over the base field, which holds because $d$ lies in $K$. It feeds the construction of a Hopf-algebra (finite flat group scheme) description of the $n$-torsion of such a curve in [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [NeZero n]
    (d : K) (hd : d * d = c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ et : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n
        ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ P Q, et (P + Q) = et P * et Q) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (P : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n),
        ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
        = σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by sorry
