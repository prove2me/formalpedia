-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/5a8e45b4-b31e-52fa-8fe8-311cc5540c47
-- title:
--   #Aut(E)=#μ₄(F) when j(E)=1728
-- statement:
--   Let $F$ be a field in which $2\neq 0$ and $3\neq 0$, and let $E$ be a Weierstrass curve over $F$ which is elliptic in Mathlib's sense (its discriminant $\Delta$ is a unit, so that the $j$-invariant is defined) and satisfies $E.j = 1728$. The assertion is an equality of natural-number cardinalities: the stabiliser of $E$ for the multiplicative action of the group `WeierstrassCurve.VariableChange F` of admissible changes of variable $(u,r,s,t)$ with $u \in F^\times$ on Weierstrass curves over $F$ has the same cardinality as the group `rootsOfUnity 4 F` of fourth roots of unity in $F^\times$, i.e. $\mathrm{Nat.card}$ of the two groups agree. Thus the $F$-rational automorphism group of the Weierstrass model $E$, realised as a stabiliser subgroup, is counted by $\#\mu_4(F)$; the statement is an equality of cardinals only, no group isomorphism being asserted.
--
--   This is the $j = 1728$ case of the classical computation of the automorphism group of an elliptic curve in characteristic different from $2$ and $3$ (Silverman, Arithmetic of Elliptic Curves, III.10.1), where $\mathrm{Aut}(E)$ has order $4$ if $-1$ is a square in $F$ and order $2$ otherwise. It feeds the $\#\mathrm{Aut}$ bookkeeping used in mass-formula style counts of elliptic curves over finite fields, and is cited by [`WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth`](thm.html#WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth) and [`WeierstrassCurve.natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728`](thm.html#WeierstrassCurve.natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) =
      Nat.card (rootsOfUnity 4 F) := by sorry
