-- Prove2me | Theorems.Thm_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv
-- name    : WeierstrassCurve.VariableChange.exists_addEquiv_affine_point_baseChange_gal_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/173d633f-422d-5803-bb24-300bd28c1110
-- title:
--   Galois equivariance of the variable-change isomorphism on ̄ K-points
-- statement:
--   Let $K$ be a field of characteristic zero, let $W$ be a Weierstrass curve over $K$, and let $C$ be a variable change over $K$ (a quadruple $(u,r,s,t)$ with $u$ a unit of $K$). Writing $\overline K$ for `AlgebraicClosure K` and equipping it with classical decidable equality, the assertion is that there exists an isomorphism of additive groups $e$ from the group of points of the base change to $\overline K$ of the transformed curve $C \cdot W$ — that is, the point at infinity together with the nonsingular affine points of the Weierstrass equation of $C \cdot W$ over $\overline K$ — onto the corresponding group of points of the base change of $W$ to $\overline K$, with the following property: for every $K$-algebra automorphism $\sigma$ of $\overline K$ and every point $P$ of $((C \cdot W)_{\overline K})$, one has $e(\sigma \cdot P) = \sigma \cdot e(P)$, the actions being the coordinatewise ones of $\sigma$ on points. Thus the existential asserts the existence of a $\mathrm{Gal}(\overline K/K)$-equivariant group isomorphism between the two groups of $\overline K$-points.
--
--   This is the statement that a change of Weierstrass coordinates defined over the base field transports $\overline K$-points compatibly with the Galois action, the equivariance being visible in the classical change-of-variables formulas $x = u^2x' + r$, $y = u^3y' + u^2sx' + t$ with $u,r,s,t \in K$. It is used to transport Galois-equivariant structure on torsion along a variable change, as in [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.VariableChange.exists_addEquiv_affine_point_baseChange_gal_equiv
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ e : ((C • W)⁄(AlgebraicClosure K)).Point ≃+ (W⁄(AlgebraicClosure K)).Point,
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) P,
        e (σ • P) = σ • (e P) := by sorry
