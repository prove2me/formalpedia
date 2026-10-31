-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_ring_equality_density_zero
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.ring_equality_density_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:52:36.39706+00:00
-- url     : https://prove2.me/theorems/ca91d542-90db-4566-9f78-015fc3a765ca
-- title:
--   Ring equality has density zero among positive even integers
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$. For each positive even cutoff $N$, let
--
--   $$f_N=\frac2N\#\{n\in\{2,4,\ldots,N\}:G_n=U_2(R_n)\}.$$
--
--   Then $f_N\to0$ along positive even $N\to\infty$. Equivalently,
--
--   $$\lim_{M\to\infty}f_{2(M+1)}=0.$$
--
--   The numerator counts precisely the even parameters with full matrix-group equality. This is the density part of introduction result (B).
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 13, Corollary 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Corollary 5.5, PDF pp.13-15: natural density along all positive even
cutoffs, with a real fraction. Also covers the density component of result (B). -/
theorem ring_equality_density_zero :
    Filter.Tendsto (fun M : ℕ => equalityFraction (2 * (M + 1)))
      Filter.atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
