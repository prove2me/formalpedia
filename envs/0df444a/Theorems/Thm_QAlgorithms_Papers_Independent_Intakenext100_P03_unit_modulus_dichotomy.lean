-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_unit_modulus_dichotomy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.unit_modulus_dichotomy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:51:28.193258+00:00
-- url     : https://prove2.me/theorems/f3142b26-2a23-422b-a1a9-6cdd256e1ecb
-- title:
--   Unit-modulus elements of the synthesis ring
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$. Write $n=2^ks$, where $k\ge1$ and $s$ is positive odd, and set $S_n=\{r\in R_n:|r|=1\}$. Both conclusions hold:
--
--   $$\begin{aligned}
--   (\exists t\ge1:\ 2^t\equiv-1\pmod s)&\Longrightarrow S_n=\{\zeta_{2n}^{\,j}:0\le j<2n\},\\
--   \neg(\exists t\ge1:\ 2^t\equiv-1\pmod s)&\Longrightarrow\exists r\in S_n\ \forall m\ge1,\ r^m\ne1.
--   \end{aligned}$$
--
--   The first set is the roots of unity in $\mathbb Q(\zeta_{2n})$. The case $s=1$ is included. This determines when the phase subgroup has an element of infinite order.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 13, Theorem 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Theorem 5.3, PDF p.13, proof pp.23-27: both directions; infinite order
means no positive natural power is 1. Includes odd part s=1. -/
theorem unit_modulus_dichotomy (n k s : ℕ) (hk : 1 ≤ k) (hs : 0 < s)
    (hodd : Odd s) (hfactor : n = 2 ^ k * s) :
    (MinusOneIsTwoPower s → unitPhases n = finitePhases n) ∧
    (¬ MinusOneIsTwoPower s → ∃ r ∈ unitPhases n,
      ∀ m : ℕ, 0 < m → r ^ m ≠ 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
