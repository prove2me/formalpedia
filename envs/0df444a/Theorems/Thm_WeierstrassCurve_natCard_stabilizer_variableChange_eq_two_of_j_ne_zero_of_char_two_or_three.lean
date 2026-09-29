-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/4c98343f-c909-5f64-952c-89f3706e131d
-- title:
--   Elliptic curves with j ≠ 0 in characteristic 2 or 3 have two automorphisms
-- statement:
--   Let $F$ be a field whose characteristic is $2$ or $3$ (that is, `ringChar F` equals $2$ or equals $3$), and let $E$ be a Weierstrass curve over $F$ which is elliptic, i.e. whose discriminant is a unit, so that its $j$-invariant `E.j` is defined. Assume $E.j \neq 0$. The group `WeierstrassCurve.VariableChange F` of admissible changes of variables $(u, r, s, t)$ with $u \in F^\times$ and $r, s, t \in F$ acts on Weierstrass curves over $F$; the assertion is that the stabiliser of $E$ under this action is a finite group of cardinality exactly $2$, the natural-number cardinality `Nat.card` of the stabiliser subgroup being $2$. Equivalently, the only changes of variables carrying the Weierstrass equation of $E$ to itself are the identity $(1,0,0,0)$ and one further involution. Note that in characteristic $2$ or $3$ one has $1728 = 0$ in $F$, so the hypothesis $j \neq 0$ is the same as $j \notin \{0, 1728\}$.
--
--   This is the case of characteristic $2$ or $3$ of the classical computation of the automorphism group of an elliptic curve in Weierstrass form (Silverman, Theorem III.10.1): for $j \neq 0, 1728$ the automorphism group of $(E, O)$ over the base field is $\{\pm 1\}$. Together with its companion in characteristic $\neq 2, 3$ it is used in the construction of equivariant torsion models and reductions attached to a given $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
    {F : Type*} [Field F] (hF : ringChar F = 2 ∨ ringChar F = 3)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by sorry
