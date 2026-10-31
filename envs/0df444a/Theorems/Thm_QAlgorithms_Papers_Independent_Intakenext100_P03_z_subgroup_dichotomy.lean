-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_z_subgroup_dichotomy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.z_subgroup_dichotomy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:52:07.102988+00:00
-- url     : https://prove2.me/theorems/e109b8d4-bcbb-4277-84d5-e99d4440438c
-- title:
--   Equality or infinitude of the two z-rotation subgroups
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$. Write $n=2^ks$ with $k\ge1$ and positive odd $s$. Let $D_n$ and $\Delta_n$ be the actual z-rotation subgroups of $G_n$ and $U_2(R_n)$, respectively. Then
--
--   $$\begin{aligned}
--   (\exists t\ge1:\ 2^t\equiv-1\pmod s)&\Longrightarrow\Delta_n=D_n=\{U_z(\pi j/n):0\le j<2n\},\\
--   \neg(\exists t\ge1:\ 2^t\equiv-1\pmod s)&\Longrightarrow |\Delta_n|=\infty\ \text{ and }G_n\ne U_2(R_n).
--   \end{aligned}$$
--
--   This supplies an obstruction to full ring equality. The positive branch asserts only equality of the z-subgroups.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 13, Corollary 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Corollary 5.4, PDF p.13. The congruence implies equality of z-subgroups,
not full-group equality; its failure implies infinity and full-group inequality. -/
theorem z_subgroup_dichotomy (n k s : ℕ) (hk : 1 ≤ k) (hs : 0 < s)
    (hodd : Odd s) (hfactor : n = 2 ^ k * s) :
    (MinusOneIsTwoPower s →
      zRotationsIn (ringUnitaries n) = zRotationsIn (cyclotomicGroup n : Set Mat) ∧
      zRotationsIn (ringUnitaries n) = finiteZRotations n) ∧
    (¬ MinusOneIsTwoPower s →
      (zRotationsIn (ringUnitaries n)).Infinite ∧
      (cyclotomicGroup n : Set Mat) ≠ ringUnitaries n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
