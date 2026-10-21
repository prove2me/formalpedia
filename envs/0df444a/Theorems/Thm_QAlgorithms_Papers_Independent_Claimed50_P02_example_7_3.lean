-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_example_7_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.example_7_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:34:36.78613+00:00
-- url     : https://prove2.me/theorems/72a6597c-61a6-4513-9273-f7862d40dbaa
-- title:
--   Example 7.3: exact 1→3 asymmetric qutrit cloning region
-- statement:
--   A real triple $r$ is physically realizable for qutrit $1\to3$ cloning if some CPTP channel has marginals $\rho\mapsto r_i\rho+(1-r_i)I/3$ on every density matrix. Allow negative $r_i$. Take $a\in\mathbb R$, $B\in\operatorname{Herm}(2)$ and $C,D\in\operatorname{Herm}(3)$, corresponding to the source's four blocks. With one-based entries, the exact region is
--   $$\mathcal R_3=\{L_3(a,B,C,D):a\ge0,\ B,C,D\succeq0,\ D_{11}+D_{22}+D_{33}+2(C_{11}+C_{22}+C_{33})+5(B_{11}+B_{22})+8a=1\}.$$
--   The affine map is
--   $$\begin{aligned}
--   8(L_3)_1={}&3D_{11}+6C_{11}+15B_{11}+24a+3D_{22}+12D_{33}+6C_{22}+24C_{33}+15B_{22}-4,\\
--   8(L_3)_2={}&3D_{11}+6C_{11}+15B_{11}+24a+11D_{22}+2\sqrt2(D_{23}+D_{32})+4D_{33}+22C_{22}+4\sqrt2(C_{23}+C_{32})+8C_{33}+15B_{22}-4,\\
--   8(L_3)_3={}&9D_{11}+21C_{11}+15B_{11}+24a+8C_{33}+15B_{22}+5D_{22}+7C_{22}+4D_{33}\\
--   &+2\sqrt3(D_{12}+D_{21})-\sqrt2(D_{23}+D_{32})-\sqrt6(D_{31}+D_{13})\\
--   &+\sqrt{15}(C_{12}+C_{21})+\sqrt{30}(C_{31}+C_{13})+\sqrt2(C_{23}+C_{32})-4.
--   \end{aligned}$$
--   Hermiticity makes every displayed coordinate real. This is an iff between physical realizability and the explicitly normalized affine PSD-block description.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 43, Example 7.3: exact 1→3 asymmetric qutrit cloning region

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper pp.43–44, Example 7.3: physical qutrit cloning iff the displayed
blocks exist. The trace normalization is 1, as in Eq.(166). -/
theorem example_7_3 (r : Fin 3 → ℝ) :
    RealizableCloning 3 r ↔
      ∃ (A : ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) (C D : Matrix (Fin 3) (Fin 3) ℂ),
        0 ≤ A ∧ B.PosSemidef ∧ C.PosSemidef ∧ D.PosSemidef ∧
        (D 0 0).re + 2*(C 0 0).re + 5*(B 0 0).re + 8*A +
          (D 1 1).re + (D 2 2).re + 2*(C 1 1).re + 2*(C 2 2).re + 5*(B 1 1).re = 1 ∧
        r = qutritCloneCoordinates A B C D := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
