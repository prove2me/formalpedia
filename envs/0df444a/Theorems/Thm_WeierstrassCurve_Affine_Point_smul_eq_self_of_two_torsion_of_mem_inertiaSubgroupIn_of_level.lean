-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level
-- name    : WeierstrassCurve.Affine.Point.smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/3feb2545-c49e-599c-946f-c69892b4211c
-- title:
--   Inertia fixes node-reducing 2-torsion of integral level
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ and let $q$ be a prime with $q \neq 2$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$, viewed in $\overline{\mathbb Q}$, is a non-unit of $A$. Let $x_0, y_0 \in A$ satisfy the two partial-derivative conditions $2y_0 + a_1 x_0 + a_3 = 0$ and $a_1 y_0 = 3x_0^2 + 2a_2 x_0 + a_4$, the node condition $v_A(b_2 + 12 x_0) = 1$ (so $b_2 + 12x_0$ is a unit of $A$), and $v_A\bigl(y_0^2 + a_1 x_0 y_0 + a_3 y_0 - (x_0^3 + a_2 x_0^2 + a_4 x_0 + a_6)\bigr) < 1$, where $v_A$ is the valuation attached to $A$. Let $\sigma$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ belonging to the image, under the inclusion of the decomposition subgroup of $A$ over $\mathbb Q$, of the inertia subgroup of $A$ over $\mathbb Q$, and suppose $\sigma x_0 = x_0$. Let $(x,y)$ be a nonsingular affine point of the base change of $W$ along $\mathbb Z \to \mathbb Q$ to $\overline{\mathbb Q}$, with witness $h$, such that the point $P = (x,y)$ satisfies $2 \cdot P = 0$ in the group of points, $v_A(x - x_0) < 1$, and $v_A(x - x_0) = v_A(q)^k$ for some natural number $k$. Then $\sigma \cdot P = P$.
--
--   This is the $2$-torsion case of the statement that inertia at a prime of multiplicative reduction acts trivially on torsion points whose distance to the node has valuation an integral power of $q$ — the valuation-theoretic substitute for the Tate-curve computation behind the Néron–Ogg–Shafarevich criterion for unramifiedness of the mod $\ell$ representation. It feeds into [`WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd`](thm.html#WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd), and its proof invokes the quadratic relation [`WeierstrassCurve.valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt`](thm.html#WeierstrassCurve.valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt) between $v_A(x - x_0)$ and the valuation of the defining polynomial at the critical centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.Point.smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (hσx₀ : σ x₀ = x₀)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : 2 • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1)
    (k : ℕ) (hlev : A.valuation (x - x₀) = A.valuation (q : AlgebraicClosure ℚ) ^ k) :
    σ • Point.some x y h = Point.some x y h := by sorry
