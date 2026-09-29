-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/aba05817-c881-564b-8b65-d132d45fa19b
-- title:
--   Two variable changes stabilise E when j ≠ 0, 1728
-- statement:
--   Let $F$ be a field in which $2 \ne 0$ and $3 \ne 0$, and let $E$ be a Weierstrass curve over $F$, given by coefficients $a_1, a_2, a_3, a_4, a_6$, which is elliptic in the sense that its discriminant $\Delta(E)$ is a unit of $F$, so that the invariant $j(E) = c_4(E)^3/\Delta(E)$ is defined. Assume $j(E) \ne 0$ and $j(E) \ne 1728$. The group $\mathrm{VariableChange}(F)$ of admissible changes of variable over $F$ consists of quadruples $(u, r, s, t)$ with $u \in F^\times$ and $r, s, t \in F$, acting on Weierstrass curves over $F$ in the usual way (the substitution $x \mapsto u^2 x + r$, $y \mapsto u^3 y + u^2 s x + t$). The assertion is that the stabiliser of $E$ for this action, i.e. the set of $(u,r,s,t)$ carrying the given Weierstrass equation to itself, is finite of cardinality exactly $2$; equivalently, the only such changes of variable are the identity and one further element. (The statement is phrased with `Nat.card`, so the equality $=2$ includes the finiteness of the stabiliser.)
--
--   This is the classical computation of the automorphism group $\mathrm{Aut}_F(E, O) = \{\pm 1\}$ for an elliptic curve with $j \ne 0, 1728$ over a field of characteristic different from $2$ and $3$, in the concrete form of the stabiliser of a Weierstrass equation under admissible changes of variable. It is used, together with the companion computations for $j = 0$ and $j = 1728$, in counting points of modular curves and their rigid data, and in producing equivariant torsion data attached to a curve with prescribed $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by sorry
