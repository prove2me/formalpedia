-- Prove2me | Theorems.Thm_WeierstrassCurve_valuation_slope_sub_slope_neg_of_shallow
-- name    : WeierstrassCurve.valuation_slope_sub_slope_neg_of_shallow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/115d3c0f-5a7e-5385-b62a-5c9d0f929c96
-- title:
--   Negation flips the branch slope at a shallow node reduction
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, with $v =$ `A.valuation` its associated multiplicatively written valuation (so $v(z)=1$ for units of $A$ and $v(z)<1$ for elements of the maximal ideal). Let $x_0, y_0 \in A$ satisfy the two partial-derivative equations $2y_0 + a_1 x_0 + a_3 = 0$ and $a_1 y_0 = 3x_0^2 + 2a_2 x_0 + a_4$ (the images of the coefficients of $W$ in $\overline{\mathbb{Q}}$ being understood), together with the node condition $v(b_2 + 12 x_0) = 1$, where $b_2 = a_1^2 + 4a_2$. Let $(x,y)$ be a nonsingular point of the affine curve attached to the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$ and then to $\overline{\mathbb{Q}}$, that is, $(x,y)$ satisfies the Weierstrass equation and the two partials do not both vanish at it. Assume $v(x - x_0) < 1$ and the shallowness condition $$v\bigl(y_0^2 + a_1 x_0 y_0 + a_3 y_0 - (x_0^3 + a_2 x_0^2 + a_4 x_0 + a_6)\bigr) < v(x-x_0)^2 .$$ Then the two slopes $(y - y_0)/(x - x_0)$ and $(\mathrm{negY}(x,y) - y_0)/(x - x_0)$, where $\mathrm{negY}(x,y) = -y - a_1 x - a_3$ is the $y$-coordinate of the negative of $(x,y)$, differ by a unit: the valuation of their difference is $1$.
--
--   This is the statement that, at a point reducing to the node $(x_0,y_0)$ with prescribed shallowness, passing from $P$ to $-P$ exchanges the two branches through the node, since the difference of the branch slopes is $2t + a_1$ whose square is $b_2 + 12x_0$ up to the curve equation, hence a unit. It is used in [`WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd`](thm.html#WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd), in the analysis of torsion points lying outside the identity component of the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_valuation_slope_sub_slope_neg_of_shallow.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.valuation_slope_sub_slope_neg_of_shallow
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    A.valuation ((y - y₀) / (x - x₀)
      - (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.negY x y - y₀) / (x - x₀)) = 1 := by sorry
