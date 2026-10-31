-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_residue_cancellation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.residue_cancellation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:56:29.166059+00:00
-- url     : https://prove2.me/theorems/09c4e02d-d957-472a-a4ae-2172092a2933
-- title:
--   Finite residue cancellation at the prime above two
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   Here $n\in\{2,4,6,8,12\}$. Let $\mathfrak p$ be the unique prime of $\mathbb Z[\zeta_{2n}]$ above $2$. Its additive ideal-normalized valuation is $v_{\mathfrak p}$, with $v_{\mathfrak p}(0)=+\infty$. Define $\mu(x,y)=-\min(v_{\mathfrak p}(x),v_{\mathfrak p}(y))$ and $\mu_n=v_{\mathfrak p}(1+i)$. A normalized pair has finite complexity even when a coordinate is zero. Let $d=\varphi(2n)$, where $\varphi$ is Euler's totient. Let $a,b$ be actual representatives $\sum_{j=0}^{d-1}a_j\zeta_{2n}^j$ with every coefficient $a_j\in\{0,1\}$, and similarly for $b$. Assume $v_{\mathfrak p}(a)=v_{\mathfrak p}(b)=0$ and $|a|^2+|b|^2\in2\mathbb Z[\zeta_{2n}]$. Then
--
--   $$\exists k\in\{1,\ldots,2n\},\qquad 2v_{\mathfrak p}(a+\zeta_{2n}^{\,k}b)>v_{\mathfrak p}(2).$$
--
--   The inequality preserves $+\infty$ if the sum vanishes. The mod-2 condition applies to the whole norm sum. This finite cancellation statement is asserted without assuming the paper's MAGMA verification as a certificate.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 22, Lemma 7.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Lemma 7.5, PDF pp.21-22, MAGMA evidence p.24. Representatives are actual
binary-coordinate algebraic integers. The mod-2 condition applies to the whole
norm sum. Multiplication by 2 retains +infinity when the sum vanishes. -/
theorem residue_cancellation (n : ℕ) (hn : SmallParameter n)
    (a b : ℂ) (ha : IsBinaryRepresentative n a) (hb : IsBinaryRepresentative n b)
    (hva : primeValuation n a = 0) (hvb : primeValuation n b = 0)
    (heven : NormSumEven n a b) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 * n ∧
      primeValuation n (2 : ℂ) < 2 * primeValuation n (a + cyclotomicRoot (2 * n) ^ k * b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
