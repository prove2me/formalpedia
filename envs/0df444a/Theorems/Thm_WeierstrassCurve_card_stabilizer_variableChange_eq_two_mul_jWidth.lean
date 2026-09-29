-- Prove2me | Theorems.Thm_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth
-- name    : WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/45221494-384f-591f-afc4-fad516c935f4
-- title:
--   Order of the automorphism group of an elliptic curve
-- statement:
--   Let $K$ be an algebraically closed field whose characteristic is neither $2$ nor $3$ (stated as $\operatorname{ringChar} K \neq 2$ and $\operatorname{ringChar} K \neq 3$), and let $W$ be a Weierstrass curve over $K$ that is elliptic, i.e. carries the `IsElliptic` instance (invertible discriminant). The group `WeierstrassCurve.VariableChange K` of admissible changes of variable $(u,r,s,t)$, $u$ a unit, acts on Weierstrass curves over $K$; the assertion is that the cardinality, as a `Nat.card`, of the stabiliser of $W$ under this action equals $2 \cdot \mathrm{jWidth}(j(W))$, where $\mathrm{jWidth}(j)$ is by definition $3$ if $j = 0$, $2$ if $j = 1728$, and $1$ otherwise. Thus the automorphism group of $W$, realised as the subgroup of variable changes fixing the equation of $W$, has order $6$ when $j(W) = 0$, order $4$ when $j(W) = 1728$, and order $2$ in all remaining cases.
--
--   This is the classical determination of $\#\operatorname{Aut}(E)$ for an elliptic curve over an algebraically closed field of characteristic prime to $6$. The half-order $\mathrm{jWidth}(j)$ is the ramification weight attached to the points $j = 0$ and $j = 1728$ of the $j$-line, and the result is used in the degree and index estimates for modular curves of full level, notably in bounding the index of a subgroup by the degree of $j$ over the relevant base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth.lean

import Mathlib
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) W) =
      2 * ModularCurve.jWidth W.j := by sorry
