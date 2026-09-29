-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq
-- name    : WeierstrassCurve.exists_variableChange_of_isShortNF_of_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/a8c7dab4-6c0b-59a6-86d3-fd5047717b11
-- title:
--   Twist comparison of short Weierstrass curves via a square root
-- statement:
--   Let $F$ be a field and let $E, E'$ be Weierstrass curves over $F$ both in short normal form, i.e. with $a_1 = a_2 = a_3 = 0$, so that they are given by $y^2 = x^3 + a_4 x + a_6$ and $y^2 = x^3 + a_4' x + a_6'$ respectively. Assume all four remaining coefficients are nonzero: $a_4 \neq 0$, $a_6 \neq 0$, $a_4' \neq 0$, $a_6' \neq 0$. Assume further the cross-relation $a_4^3 (a_6')^2 = (a_4')^3 a_6^2$ (the condition expressing equality of the two $j$-invariants in this normalisation), and suppose there is an element $s \in F$ with $s^2 \cdot (a_6' a_4) = a_6 a_4'$, that is, $s^2$ is the ratio $(a_6/a_6')/(a_4/a_4')$. The conclusion is that there exists a Weierstrass variable change $C$ over $F$ (a quadruple $(u, r, s, t)$ with $u$ a unit) whose action on $E$ yields exactly $E'$, i.e. $C \bullet E = E'$.
--
--   This is the explicit isomorphism criterion for short Weierstrass curves with equal $j$-invariant and $j \neq 0, 1728$: two such curves are twists of one another, and they are $F$-isomorphic precisely when the twisting ratio is a square in $F$, here witnessed by the given $s$. It is the short-form core of the general comparison [`WeierstrassCurve.exists_variableChange_of_j_eq_of_sq`](thm.html#WeierstrassCurve.exists_variableChange_of_j_eq_of_sq), which is obtained from it by reduction to short normal form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {F : Type*} [Field F]

theorem exists_variableChange_of_isShortNF_of_sq (E E' : WeierstrassCurve F)
    [E.IsShortNF] [E'.IsShortNF]
    (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0) (ha₄' : E'.a₄ ≠ 0) (ha₆' : E'.a₆ ≠ 0)
    (hrel : E.a₄ ^ 3 * E'.a₆ ^ 2 = E'.a₄ ^ 3 * E.a₆ ^ 2)
    {s : F} (hs : s ^ 2 * (E'.a₆ * E.a₄) = E.a₆ * E'.a₄) :
    ∃ C : VariableChange F, C • E = E' := by sorry
