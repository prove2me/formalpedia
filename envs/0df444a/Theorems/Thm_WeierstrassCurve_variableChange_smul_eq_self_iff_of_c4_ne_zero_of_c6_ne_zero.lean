-- Prove2me | Theorems.Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
-- name    : WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c2402a71-5a06-5aa9-b520-f0a516d8fb94
-- title:
--   Stabiliser of a Weierstrass model with c₄,c₆≠ 0
-- statement:
--   Let $F$ be a field in which $2\neq 0$ and $3\neq 0$, let $E$ be a Weierstrass curve over $F$ (a tuple of coefficients $a_1,a_2,a_3,a_4,a_6$) whose invariants satisfy $c_4(E)\neq 0$ and $c_6(E)\neq 0$, and let $C=(u,r,s,t)$ be an admissible change of variables over $F$, with $u$ a unit of $F$ and $r,s,t\in F$. The assertion is an equivalence: the transformed Weierstrass curve $C\cdot E$ equals $E$ — equality of all five coefficients, for the Mathlib action of `WeierstrassCurve.VariableChange` on `WeierstrassCurve` — if and only if either $C$ is the identity change of variables $(1,0,0,0)$ or $C$ is the change of variables $(-1,\,0,\,-a_1(E),\,-a_3(E))$, the latter being the negation automorphism $(x,y)\mapsto(x,-y-a_1x-a_3)$ of the model. Thus the stabiliser of the model is described by listing its two elements, rather than merely by its order; no smoothness or nonvanishing hypothesis on the discriminant is imposed beyond $c_4\neq0$ and $c_6\neq0$.
--
--   This is the computation of the automorphism group of a Weierstrass model in the classical case $j\neq 0,1728$, where it is $\{\pm 1\}$. It is used in the moduli description of modular curves, being cited in the identification of orbits of Weierstrass models with the same $j$-invariant, in the count of moduli points above a given $j$-value, and in the analysis of points fixed by the action on full-level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (E : WeierstrassCurve F)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0) (C : WeierstrassCurve.VariableChange F) :
    C • E = E ↔ C = 1 ∨ C = ⟨-1, 0, -E.a₁, -E.a₃⟩ := by sorry
