-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_ring_characterization_small
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.ring_characterization_small
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:50:07.961627+00:00
-- url     : https://prove2.me/theorems/bca45d09-4f29-4a7b-86ee-cbd730124166
-- title:
--   Exact ring characterization for five small parameters
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$. For each $n\in\{2,4,6,8,12\}$, let $U_2(R_n)$ denote the actual $2\times2$ unitary matrices whose entries lie in $R_n$. Then
--
--   $$G_n=U_2(R_n).$$
--
--   Both inclusions preserve absolute phase. This is the complete five-case theorem; the cases $n=2,12$ are new here, while p.12 credits prior work for $4,6,8$. No finite-verification certificate is a hypothesis.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 12, Theorem 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Theorem 5.1, PDF p.12, proof pp.18-24. Equality is of actual matrices,
including absolute phase; no computational-verification premise is imposed. -/
theorem ring_characterization_small (n : ℕ) (hn : SmallParameter n) :
    (cyclotomicGroup n : Set Mat) = ringUnitaries n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
