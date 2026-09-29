-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/e8b3645c-e61f-5152-8618-6290f96ac514
-- title:
--   Twelve automorphisms when j=0 in characteristic 3
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $3$, and let $E$ be a Weierstrass curve over $F$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, which is elliptic in the sense that its discriminant is a unit of $F$, so that its $j$-invariant is defined. Assume $j(E)=0$. The group `WeierstrassCurve.VariableChange F` of admissible changes of variables over $F$, whose elements are quadruples $(u,r,s,t)$ with $u \in F^{\times}$ and $r,s,t \in F$, acts on Weierstrass curves over $F$; the assertion is that the stabiliser of $E$ for this action is finite of cardinality exactly $12$ (the natural-number cardinality `Nat.card` of the stabiliser subgroup equals $12$). Equivalently, $E$ admits precisely $12$ automorphisms as a Weierstrass model over $F$.
--
--   This is the characteristic-$3$ case of the classical computation of the automorphism group of a Weierstrass model over an algebraically closed field: for $p = 3$ and $j = 0$ (where $0 = 1728$) the curve is supersingular and its automorphism group has order $12$, being an extension of the group of fourth roots of unity by a group of order $3$. It feeds the general count of the stabiliser in [`WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_mul_jWidthChar`](thm.html#WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_mul_jWidthChar), which in turn governs the ramification of maps of modular curves above the point $j = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
    {F : Type*} [Field F] [IsAlgClosed F] [CharP F 3]
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 12 := by sorry
