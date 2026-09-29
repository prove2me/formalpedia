-- Prove2me | Theorems.Thm_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero
-- name    : WeierstrassCurve.mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c9190df0-8485-5e33-bce4-f6976b5c8500
-- title:
--   Stabiliser of y²=x³+a₆ under admissible changes of variables
-- statement:
--   Let $F$ be a field in which $2 \ne 0$ and $3 \ne 0$, and let $E$ be a Weierstrass curve over $F$ which is in short normal form, i.e. $a_1 = a_2 = a_3 = 0$, so that $E$ is given by $y^2 = x^3 + a_4 x + a_6$; assume moreover $a_4 = 0$ and $a_6 \ne 0$. Let $C = (u, r, s, t)$, with $u \in F^\times$ and $r, s, t \in F$, be an admissible change of variables, acting on Weierstrass curves by Mathlib's scalar action of the group `WeierstrassCurve.VariableChange F`. The assertion is that $C$ lies in the stabiliser of $E$ for this action, i.e. $C \bullet E = E$ as Weierstrass equations, if and only if $r = 0$, $s = 0$, $t = 0$ and $u^6 = 1$ in $F$. Thus the stabiliser of the equation $y^2 = x^3 + a_6$ with $a_6 \ne 0$ consists exactly of the pure scalings by sixth roots of unity. No smoothness or ellipticity hypothesis on $E$ is imposed beyond $a_6 \ne 0$.
--
--   This is the $j = 0$ case of the classical determination of the automorphism group of a Weierstrass equation in characteristic $\ne 2, 3$, with automorphisms encoded as the stabiliser of the equation under the change-of-variables group. It feeds the counting of automorphisms of curves over finite fields used in the mass-formula computations, and is cited in the construction and analysis of good models of special fibres of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₄ : E.a₄ = 0) (ha₆ : E.a₆ ≠ 0)
    (C : WeierstrassCurve.VariableChange F) :
    C ∈ MulAction.stabilizer (WeierstrassCurve.VariableChange F) E ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 6 = 1 := by sorry
