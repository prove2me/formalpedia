-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero
-- name    : WeierstrassCurve.natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/94360e34-14bb-5f74-b32c-6d79664ad265
-- title:
--   Stabiliser order divides 6 when j(E)=0
-- statement:
--   Let $F$ be a field in which $2 \neq 0$ and $3 \neq 0$, and let $E$ be a Weierstrass curve over $F$ which is elliptic (its discriminant is a unit, so that the $j$-invariant is defined) and satisfies $E.j = 0$. The group `WeierstrassCurve.VariableChange F` of Weierstrass changes of variable $(u, r, s, t)$ with $u \in F^\times$ acts on Weierstrass curves over $F$; the assertion is that the cardinality of the stabiliser of $E$ for this action — that is, the number of changes of variable carrying $E$ to itself, which is the automorphism group of $E$ as an elliptic curve over $F$ — is a natural number dividing $6$. The cardinality is taken as `Nat.card`, so the statement is about the natural number attached to the stabiliser subgroup; finiteness is not asserted separately, although divisibility by $6$ forces the stabiliser to be finite here.
--
--   This is the $j = 0$ case of the classical determination of automorphism groups of elliptic curves in characteristic $\neq 2, 3$ (where $\#\operatorname{Aut}(E) \mid 6$, with equality over a field containing the sixth roots of unity). It is used in the analysis of changes of variable fixing curves with special $j$-invariant, in the work towards the mass formula counting elliptic curves over a finite field weighted by $1/\#\operatorname{Aut}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) ∣ 6 := by sorry
