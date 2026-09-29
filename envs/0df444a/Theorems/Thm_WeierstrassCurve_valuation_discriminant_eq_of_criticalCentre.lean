-- Prove2me | Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
-- name    : WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/b5910918-395e-5f89-9c8c-0b9ad2d00dce
-- title:
--   Discriminant valuation at a nodal critical centre
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, with its associated multiplicatively written valuation $v =$ `A.valuation` (so $v(z)\le 1$ exactly for $z\in A$, and $v(z)=1$ means $z$ is a unit of $A$). Let $x_0,y_0\in\overline{\mathbb{Q}}$ both lie in $A$, and write $F(x,y) = y^2 + a_1xy + a_3y - (x^3 + a_2x^2 + a_4x + a_6)$, the coefficients being taken as elements of $\overline{\mathbb{Q}}$. Assume the two partial-derivative conditions $2y_0 + a_1x_0 + a_3 = 0$ and $a_1y_0 = 3x_0^2 + 2a_2x_0 + a_4$, so that $(x_0,y_0)$ is a critical point of $F$; assume $v(b_2 + 12x_0) = 1$, i.e. $b_2 + 12 x_0$ is a unit of $A$, where $b_2 = a_1^2 + 4a_2$; and assume $v(F(x_0,y_0)) < 1$, i.e. $F(x_0,y_0)$ lies in the maximal ideal of $A$. The conclusion is the equality of valuations $v(\Delta_W) = v(F(x_0,y_0))$, where $\Delta_W$ is the discriminant of $W$, viewed in $\overline{\mathbb{Q}}$.
--
--   This identifies the valuation of the discriminant of an integral Weierstrass model with the "depth" $v(F(x_0,y_0))$ of a node at a critical centre $(x_0,y_0)$ with non-degenerate tangent cone, giving a substitute for the Tate-curve computation $\operatorname{ord}(q_E) = \operatorname{ord}(\Delta)$. It feeds the analysis of multiplicative reduction and of the level at primes of bad reduction in the Frey-curve part of the argument, and is used by results on filtrations at a prime of multiplicative reduction and on the Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1) :
    A.valuation (W.Δ : AlgebraicClosure ℚ) =
      A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by sorry
