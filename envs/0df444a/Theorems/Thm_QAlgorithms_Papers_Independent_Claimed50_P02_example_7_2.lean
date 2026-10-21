-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_example_7_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.example_7_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:33:51.43498+00:00
-- url     : https://prove2.me/theorems/04244536-fca7-441a-912b-722c418e5af5
-- title:
--   Example 7.2: exact 1→3 asymmetric qubit cloning region
-- statement:
--   A real triple $r=(r_1,r_2,r_3)$ is physically realizable by a qubit $1\to3$ CPTP channel when its $i$th marginal is $\rho\mapsto r_i\rho+(1-r_i)I/2$ for every density matrix. No nonnegativity restriction is imposed on $r_i$. Let $a\in\mathbb R$, $B\in\operatorname{Herm}(2)$ and $C\in\operatorname{Herm}(3)$; below entries are one-based, and paired off-diagonal expressions are real. The exact region is
--   $$
--   \mathcal R_2=\{L_2(a,B,C):a\ge0,\ B\succeq0,\ C\succeq0,\ 5a+B_{11}+B_{22}+3(C_{11}+C_{22}+C_{33})=2\},
--   $$
--   where
--   $$\begin{aligned}
--   (L_2)_1&=(3C_{11}+B_{11}+5a+3C_{22}+9C_{33}+3B_{22}-3)/3,\\
--   (L_2)_2&=(6C_{11}+5B_{11}+10a+15C_{22}+3\sqrt3(C_{23}+C_{32})+9C_{33}+\sqrt3(B_{12}+B_{21})+3B_{22}-6)/6,\\
--   (L_2)_3&=(14C_{11}+5B_{11}+10a+2\sqrt2(C_{12}+C_{21})+7C_{22}+9C_{33}+2\sqrt6(C_{13}+C_{31})+\sqrt3(C_{23}+C_{32})-\sqrt3(B_{12}+B_{21})+3B_{22}-6)/6.
--   \end{aligned}$$
--   Equality of regions asserts both that every channel gives feasible coordinates and that each feasible triple has a realizing channel. It does not require every realizing channel to be equivariant.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 42, Example 7.2: exact 1→3 asymmetric qubit cloning region

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.42, Example 7.2: equality of the physical qubit cloning region and
the affine image of the PSD blocks, with the printed trace normalization 2.
No assertion that every realizing channel is already equivariant is made. -/
theorem example_7_2 (r : Fin 3 → ℝ) :
    RealizableCloning 2 r ↔
      ∃ (A : ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix (Fin 3) (Fin 3) ℂ),
        0 ≤ A ∧ B.PosSemidef ∧ C.PosSemidef ∧
        5*A + (B 0 0).re + (B 1 1).re +
          3*(C 0 0).re + 3*(C 1 1).re + 3*(C 2 2).re = 2 ∧
        r = qubitCloneCoordinates A B C := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
