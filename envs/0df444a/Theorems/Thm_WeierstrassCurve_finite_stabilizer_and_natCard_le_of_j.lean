-- Prove2me | Theorems.Thm_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j
-- name    : WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/5cd34853-8ffb-5430-90f9-2bcdf68fc269
-- title:
--   Bounds on the Weierstrass automorphism group at j=0 and j=1728
-- statement:
--   Let $F$ be a field and let $E$ be a Weierstrass curve over $F$ which is elliptic (its discriminant is a unit, so that the invariant $j$-invariant $E.j$ is defined). Consider the action of the group $\mathrm{VariableChange}\ F$ of admissible changes of Weierstrass coordinates $(u,r,s,t)$ with $u$ invertible on Weierstrass curves over $F$, and let $\mathrm{MulAction.stabilizer}$ of $E$ be the subgroup of those changes of variables carrying the equation of $E$ to itself. The theorem asserts four implications simultaneously: (i) if $6 \neq 0$ in $F$ and $E.j = 0$, then this stabiliser is finite and its cardinality is at most $6$; (ii) if $6 \neq 0$ in $F$ and $E.j = 1728$, then it is finite of cardinality at most $4$; (iii) if $F$ has characteristic $3$ and $E.j = 0$, then it is finite of cardinality at most $12$; (iv) if $F$ has characteristic $2$ and $E.j = 0$, then it is finite of cardinality at most $24$. Only upper bounds are asserted; no lower bound or exact value is claimed, and no separable closedness is assumed.
--
--   This is the upper-bound half of the classical determination of the automorphism group of an elliptic curve with extra automorphisms, for Weierstrass models over an arbitrary field rather than over a separably closed one. It is used in the construction of equivariant torsion models and reductions attached to prescribed $j$-invariants, where the finiteness and the numerical bounds control the possible automorphisms of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j
    {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 24) := by sorry
