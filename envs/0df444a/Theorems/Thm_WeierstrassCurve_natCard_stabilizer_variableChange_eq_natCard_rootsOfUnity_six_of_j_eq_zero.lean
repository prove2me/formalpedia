-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/27dc4c00-d061-5026-8db6-6cd4696128b9
-- title:
--   Automorphism count for j=0 equals #μ₆(F)
-- statement:
--   Let $F$ be a field in which $2 \neq 0$ and $3 \neq 0$, and let $E$ be a Weierstrass curve over $F$ which is elliptic (its discriminant is a unit). Assume the $j$-invariant of $E$ vanishes, $E.j = 0$. Then the stabiliser of $E$ for the action of the group `WeierstrassCurve.VariableChange F` of admissible changes of variable $(u,r,s,t)$, with $u$ a unit of $F$, on Weierstrass curves over $F$ has the same cardinality, in the sense of `Nat.card`, as the group $\mu_6(F)$ of sixth roots of unity in $F$, i.e. `rootsOfUnity 6 F`. Thus the assertion is an equality of (naive) cardinalities of the two groups, not the construction of an isomorphism between them; and the stabiliser is taken with respect to changes of variable defined over $F$ itself, so the count records the $F$-rational automorphisms of the given Weierstrass model.
--
--   This is the $j=0$ case of the classical computation of the automorphism group of an elliptic curve in characteristic different from $2$ and $3$ (Silverman, Arithmetic of Elliptic Curves, III.10.1): the automorphisms are the scalings by sixth roots of unity. It feeds the divisibility statement [`WeierstrassCurve.natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero`](thm.html#WeierstrassCurve.natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero) and the formula [`WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth`](thm.html#WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth), which enter mass-formula counts of elliptic curves over finite fields weighted by $1/\#\mathrm{Aut}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) =
      Nat.card (rootsOfUnity 6 F) := by sorry
