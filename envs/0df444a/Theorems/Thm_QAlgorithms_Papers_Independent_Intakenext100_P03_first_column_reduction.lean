-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_first_column_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.first_column_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:55:29.26597+00:00
-- url     : https://prove2.me/theorems/afd1c4c8-42d7-4dd5-94a8-2b858077613f
-- title:
--   Membership reduces to exact first-column synthesis
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$. Write $n=2^ks$, with $k\ge1$ and positive odd $s$, and assume $2^t\equiv-1\pmod s$ for some positive integer $t$. For every $U\in U_2(R_n)$,
--
--   $$U\in G_n\quad\Longleftrightarrow\quad\exists V\in G_n:\ \forall b\in\{0,1\},\ V_{b0}=U_{b0}.$$
--
--   Column equality includes absolute phase. This reduction holds under the congruence condition, beyond the five small parameters.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 19, Lemma 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Lemma 7.1, PDF pp.18-19: exact first-column equality, retaining phase,
under the congruence condition beyond the five small parameters. -/
theorem first_column_reduction (n k s : ℕ) (hk : 1 ≤ k) (hs : 0 < s)
    (hodd : Odd s) (hfactor : n = 2 ^ k * s) (hcong : MinusOneIsTwoPower s)
    (U : Mat) (hU : U ∈ ringUnitaries n) :
    U ∈ cyclotomicGroup n ↔ ∃ V ∈ cyclotomicGroup n,
      ∀ b : Bool, V b false = U b false := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
