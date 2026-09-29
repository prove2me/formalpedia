-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero
-- name    : WeierstrassCurve.exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/23409591-e096-5cb5-bb85-bd02b7625205
-- title:
--   Canonical Deuring normal form at a three-torsion point
-- statement:
--   Let $F$ be a field and $E$ a Weierstrass curve over $F$, and let $x_1,y_1,x_2,y_2 \in F$ be such that $(x_1,y_1)$ and $(x_2,y_2)$ are nonsingular points of the affine model of $E$ (with the corresponding points $P_1, P_2$ of $E(F)$), such that $3 \cdot P_1 = 0$ in the group of points and $x_1 \neq x_2$. Write $A_3 =$ `E.deuringA₃ x₁ y₁`, $m =$ `E.tangentSlope x₁ y₁` $= (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1)\,A_3^{-1}$ for the tangent slope at $P_1$, and set $\tau =$ `E.levelThreeModulus x₁ y₁ x₂` $= \mathrm{deuringA_1}(x_1,y_1)\,(x_2-x_1)\,A_3^{-1}$, $\nu =$ `E.levelThreeAbscissa x₁ y₁ x₂` $= (x_2-x_1)^3 A_3^{-2}$ and $\eta =$ `E.levelThreeOrdinate x₁ y₁ x₂ y₂` $= (y_2-y_1-m(x_2-x_1))(x_2-x_1)^3A_3^{-3}$ (inverses taken in the sense of `Ring.inverse`). The assertion is: $A_3 \neq 0$ and $\nu \neq 0$; there is a Weierstrass variable change $\kappa$ over $F$ with $u = A_3/(x_2-x_1)$, $r = x_1$, $s = m$, $t = y_1$ such that $\kappa \bullet E$ is the curve $\langle \tau,0,\nu,0,0\rangle$, that is $y^2 + \tau xy + \nu y = x^3$; the pairs $(0,0)$ and $(\nu,\eta)$ are nonsingular points of this curve; the bijection on points `Point.equivOfVariableChangeEq` attached to that equality of curves carries $(0,0)$ to $(x_1,y_1)$ and $(\nu,\eta)$ to $(x_2,y_2)$; and if moreover $3 \cdot P_2 = 0$, then $3\nu + \tau^2 + 3\tau + 3 = 0$ and $2\eta + \tau\nu + \nu \neq 0$.
--
--   This is the passage to Deuring's normal form $y^2 + \alpha xy + \beta y = x^3$ at a rational point of order three, normalised so that the second marked point has abscissa equal to $\beta$, which pins down the scaling $u$ without any root extraction and makes $(\tau,\nu,\eta)$ depend only on the triple $(E;P_1,P_2)$ up to isomorphism; the final clause records the relation satisfied when the second point also has order three, and the non-vanishing saying it is not of order two. It is used in the treatment of quotients by three-torsion subgroups, in [`WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient`](thm.html#WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_LevelThreeModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_variableChange_eq_deuringCurve_of_three_smul_eq_zero
    {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hx : x₁ ≠ x₂) :
    E.deuringA₃ x₁ y₁ ≠ 0 ∧ E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0 ∧
    ∃ κ : VariableChange F,
      ((κ.u : F) = E.deuringA₃ x₁ y₁ / (x₂ - x₁) ∧ κ.r = x₁ ∧ κ.s = E.tangentSlope x₁ y₁ ∧ κ.t = y₁) ∧
    ∃ hκ : κ • E = deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂),
    ∃ h₀ : (deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂)).toAffine.Nonsingular 0 0,
    ∃ h₂' : (deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂)).toAffine.Nonsingular
        (E.levelThreeAbscissa x₁ y₁ x₂) (E.levelThreeOrdinate x₁ y₁ x₂ y₂),
      Point.equivOfVariableChangeEq hκ (.some 0 0 h₀) = .some x₁ y₁ h₁ ∧
      Point.equivOfVariableChangeEq hκ (.some _ _ h₂') = .some x₂ y₂ h₂ ∧
      ((3 : ℤ) • (Point.some x₂ y₂ h₂) = 0 →
        3 * E.levelThreeAbscissa x₁ y₁ x₂ + E.levelThreeModulus x₁ y₁ x₂ ^ 2
          + 3 * E.levelThreeModulus x₁ y₁ x₂ + 3 = 0 ∧
        2 * E.levelThreeOrdinate x₁ y₁ x₂ y₂ + E.levelThreeModulus x₁ y₁ x₂ * E.levelThreeAbscissa x₁ y₁ x₂
          + E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0) := by sorry
