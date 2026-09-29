-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq
-- name    : WeierstrassCurve.exists_variableChange_of_legendreLambda_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/9a94bc46-7dcb-5a64-b382-45475cd64f7d
-- title:
--   Legendre modulus determines a curve with ordered 2-torsion pair
-- statement:
--   Let $F$ be a field with $2 \neq 0$ and let $E, E'$ be Weierstrass curves over $F$. Suppose $(x_1,y_1)$ and $(x_2,y_2)$ are points satisfying the nonsingularity condition for the affine model of $E$, whose associated points `Point.some` are killed by $2$ in the group $E(F)$, and with $x_1 \neq x_2$; similarly let $(x_1',y_1')$, $(x_2',y_2')$ be nonsingular points of the affine model of $E'$ killed by $2$ with $x_1' \neq x_2'$. Assume given $u \in F$ with $u^2(x_2' - x_1') = x_2 - x_1$, and assume the Legendre moduli agree: $(x_3 - x_1)/(x_2 - x_1) = (x_3' - x_1')/(x_2' - x_1')$, where $x_3 = -b_2(E)/4 - x_1 - x_2$ and $x_3' = -b_2(E')/4 - x_1' - x_2'$ are the third abscissae. Then there exist a Weierstrass variable change $\gamma$ over $F$ and a proof that $\gamma \bullet E = E'$ such that the induced bijection $E'(F) \simeq E(F)$ attached to this equality carries $(x_1',y_1')$ to $(x_1,y_1)$ and $(x_2',y_2')$ to $(x_2,y_2)$. The variable change is not asserted to have $u$ as its scaling parameter.
--
--   This is the statement that, in characteristic different from $2$, the Legendre modulus $\lambda$ is a complete invariant of a Weierstrass curve equipped with an ordered pair of distinct rational points of order two, the isomorphism being realised by an explicit change of Weierstrass coordinates respecting the marking (the square root $u$ of the ratio of abscissa differences being supplied as a hypothesis rather than extracted). It is used downstream in the comparison of marked curves under a variable change compatible with a quotient by a $2$-torsion point, and in showing that a Legendre cross-ratio expression does not degenerate when the $j$-invariant is non-constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_WeierstrassCurve_LegendreModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_variableChange_of_legendreLambda_eq {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (E E' : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂) (hP₁ : (2 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (2 : ℤ) • (Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁') (h₂' : E'.toAffine.Nonsingular x₂' y₂') (hP₁' : (2 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (2 : ℤ) • (Point.some x₂' y₂' h₂') = 0) (hx' : x₁' ≠ x₂') {u : F} (hu : u ^ 2 * (x₂' - x₁') = x₂ - x₁) (hl : E.legendreLambda x₁ x₂ = E'.legendreLambda x₁' x₂') :
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      Point.equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ := by sorry
