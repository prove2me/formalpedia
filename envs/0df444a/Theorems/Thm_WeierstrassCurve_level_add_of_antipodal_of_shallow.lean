-- Prove2me | Theorems.Thm_WeierstrassCurve_level_add_of_antipodal_of_shallow
-- name    : WeierstrassCurve.level_add_of_antipodal_of_shallow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/e4b3f28c-a3e3-50b3-be98-cc4f6706b0c3
-- title:
--   Antipodal plus shallow point at a node: level and branch
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, with associated valuation $v =$ `A.valuation` (written multiplicatively, so $v(a)=1$ means $a$ is a unit of $A$ and $v(a)<1$ that $a$ lies in the maximal ideal). Let $x_0, y_0 \in A$ satisfy $2y_0 + a_1x_0 + a_3 = 0$ and $a_1 y_0 = 3x_0^2 + 2a_2x_0 + a_4$, i.e. $(x_0,y_0)$ is a critical point of $F(x,y) = y^2 + a_1xy + a_3y - (x^3 + a_2x^2 + a_4x + a_6)$; assume $v(b_2 + 12x_0) = 1$ and $v(F_0) < 1$, where $F_0 := F(x_0,y_0)$. Let $(x_1,y_1)$ and $(x_2,y_2)$ be nonsingular affine points of the base change of $W$ to $\overline{\mathbb{Q}}$ (through $\mathbb{Q}$), both with $v(x_i - x_0) < 1$, and assume $(x_1,y_1)$ is antipodal, $v(x_1-x_0)^2 \le v(F_0)$, while $(x_2,y_2)$ is shallow, $v(F_0) < v(x_2-x_0)^2$. Then there are $x_3, y_3$ with $(x_3,y_3)$ nonsingular such that the sum of the two points in the Mathlib point group equals `Point.some x₃ y₃ h₃`, with $\bigl(v(x_3-x_0)\,v(x_2-x_0)\bigr)^2 = v(F_0)$ and $v\bigl((y_3-y_0)/(x_3-x_0) - (y_2-y_0)/(x_2-x_0)\bigr) = 1$.
--
--   This is one clause of the signed-level calculus at a node: in the Tate dictionary, where the level $v(x-x_0)$ and the branch recorded by the slope $(y-y_0)/(x-x_0)$ encode the image of a point in the component group $\mathbb{Z}/n$ of a curve of type $I_n$, it expresses that adding an antipodal point (image $n/2$) to a shallow point shifts the component by $n/2$, so that the resulting point is shallow at the complementary level and lies on the opposite branch. It is used by [`WeierstrassCurve.level_add_of_inZeroComponentAt`](thm.html#WeierstrassCurve.level_add_of_inZeroComponentAt) and by the lemmas computing levels of torsion points not in the identity component, such as [`WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt`](thm.html#WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt) and [`WeierstrassCurve.valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt`](thm.html#WeierstrassCurve.valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_level_add_of_antipodal_of_shallow.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.level_add_of_antipodal_of_shallow
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
    (hX₁ : A.valuation (x₁ - x₀) < 1)
    (hanti₁ : A.valuation (x₁ - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)))
    (hX₂ : A.valuation (x₂ - x₀) < 1)
    (hsh₂ : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₂ - x₀) ^ 2) :
    ∃ (x₃ y₃ : AlgebraicClosure ℚ)
      (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧
      (A.valuation (x₃ - x₀) * A.valuation (x₂ - x₀)) ^ 2 =
        A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) ∧
      A.valuation ((y₃ - y₀) / (x₃ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1 := by sorry
