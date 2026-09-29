-- Prove2me | Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange
-- name    : WeierstrassCurve.finite_stabilizer_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/809b9b41-6797-58b5-8308-6eda4b8ffd5b
-- title:
--   Finiteness of the variable-change stabiliser of an elliptic Weierstrass curve
-- statement:
--   Let $F$ be a field and let $E$ be a Weierstrass curve over $F$, that is, a tuple of coefficients $(a_1,a_2,a_3,a_4,a_6)$ in $F$, which is assumed elliptic in Mathlib's sense: its discriminant $\Delta(E)$ is a unit of $F$, equivalently $\Delta(E)\neq 0$. Consider the group `WeierstrassCurve.VariableChange F` of admissible changes of variable over $F$, whose elements are quadruples $(u,r,s,t)$ with $u \in F^{\times}$ and $r,s,t \in F$, together with its Mathlib multiplicative action on Weierstrass curves over $F$ by the usual substitution $x = u^{2}x' + r$, $y = u^{3}y' + u^{2}sx' + t$. The assertion is that the stabiliser of $E$ for this action, namely the subgroup of those $(u,r,s,t)$ that carry $E$ back to the same tuple of coefficients, is a finite type. No bound on its cardinality is asserted, and no restriction is placed on the characteristic of $F$; in particular characteristics $2$ and $3$ are included.
--
--   This is the finiteness half of the classical description of the automorphism group of a Weierstrass model of an elliptic curve, which classically has order dividing $24$. It is used in the construction of equivariant torsion reductions attached to a $j$-invariant, where finiteness of the geometric automorphism group of a reduced model is needed to run averaging and counting arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finite_stabilizer_variableChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.finite_stabilizer_variableChange (F : Type*) [Field F] (E : WeierstrassCurve F) [E.IsElliptic] : Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) := by sorry
