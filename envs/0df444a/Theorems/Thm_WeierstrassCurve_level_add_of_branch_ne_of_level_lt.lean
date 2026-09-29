-- Prove2me | Theorems.Thm_WeierstrassCurve_level_add_of_branch_ne_of_level_lt
-- name    : WeierstrassCurve.level_add_of_branch_ne_of_level_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/cd21347a-10f7-5720-accc-9aaa783e3449
-- title:
--   Level of a sum: opposite branches, distinct levels
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ and $A$ a valuation subring of $\overline{\mathbb Q}$, with multiplicatively written valuation $v =$ `A.valuation` (so $v(a)=1$ means $a$ is a unit of $A$ and $v(a)<1$ that $a$ lies in the maximal ideal). Let $x_0,y_0\in A$ satisfy the two critical-point equations $2y_0+a_1x_0+a_3=0$ and $a_1y_0=3x_0^2+2a_2x_0+a_4$, assume $b_2+12x_0$ is a unit, and write $F_0=y_0^2+a_1x_0y_0+a_3y_0-(x_0^3+a_2x_0^2+a_4x_0+a_6)$ with $v(F_0)<1$. Let $(x_1,y_1)$ and $(x_2,y_2)$ be nonsingular affine points of $W$ base changed from $\mathbb Z$ through $\mathbb Q$ to $\overline{\mathbb Q}$, with $v(x_2-x_0)<1$, $v(x_1-x_0)<v(x_2-x_0)$, $v(F_0)<v(x_1-x_0)^2$, and with the slopes $t_i=(y_i-y_0)/(x_i-x_0)$ satisfying $v(t_1-t_2)=1$. Then the group-law sum `Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂` is again an affine point `Point.some x₃ y₃ h₃`, for some nonsingular $(x_3,y_3)$ with $v(x_3-x_0)\,v(x_2-x_0)=v(x_1-x_0)$ and $v(t_3-t_1)<1$, where $t_3=(y_3-y_0)/(x_3-x_0)$.
--
--   This is one clause of the signed-level calculus at a multiplicative place: with $(x_0,y_0)$ a critical point lifting the node of the reduction, $v(x-x_0)$ measures the level of an affine point and the valuation of the slope difference records its branch, so that the conclusion is the additivity of the component-group image of a point (the Tate parametrisation picture for a curve of type $I_n$) in the case of two points on opposite branches at distinct levels, the sum inheriting the branch of the deeper point. It feeds the level computations [`WeierstrassCurve.level_add_of_inZeroComponentAt`](thm.html#WeierstrassCurve.level_add_of_inZeroComponentAt) and the valuation identities for torsion points outside the identity component used in the ramification analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_level_add_of_branch_ne_of_level_lt.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.level_add_of_branch_ne_of_level_lt
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₂ : A.valuation (x₂ - x₀) < 1) (hlt : A.valuation (x₁ - x₀) < A.valuation (x₂ - x₀))
    (hsh₁ : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₁ - x₀) ^ 2)
    (hbr : A.valuation ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1) :
    ∃ (x₃ y₃ : AlgebraicClosure ℚ)
      (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧
      A.valuation (x₃ - x₀) * A.valuation (x₂ - x₀) = A.valuation (x₁ - x₀) ∧
      A.valuation ((y₃ - y₀) / (x₃ - x₀) - (y₁ - y₀) / (x₁ - x₀)) < 1 := by sorry
