-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_z_rotations_in_group
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.z_rotations_in_group
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:50:47.035037+00:00
-- url     : https://prove2.me/theorems/1447169b-6252-4ff9-b083-7b67540b66e1
-- title:
--   The z-axis rotations in the generated group
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$. The subgroup $D_n$ of actual matrices of the form $U_z(\theta)$ in $G_n$ satisfies
--
--   $$D_n=\{U_z(\pi j/n):j=0,\ldots,2n-1\}.$$
--
--   Matrices merely proportional to z-rotations are not included by definition. This restricts the available z-rotation angles exactly.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 12, Theorem 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Theorem 5.2, PDF pp.12-13: the actual z-axis rotations in G_n. -/
theorem z_rotations_in_group (n : ℕ) (hn : 0 < n) (heven : Even n) :
    zRotationsIn (cyclotomicGroup n : Set Mat) = finiteZRotations n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
