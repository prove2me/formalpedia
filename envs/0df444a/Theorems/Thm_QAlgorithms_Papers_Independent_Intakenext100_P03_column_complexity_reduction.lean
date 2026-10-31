-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_column_complexity_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.column_complexity_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:57:05.9212+00:00
-- url     : https://prove2.me/theorems/332aef85-fb72-4e99-ae61-d14e1c445872
-- title:
--   Strict reduction of normalized column complexity
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   Here $n\in\{2,4,6,8,12\}$. Let $\mathfrak p$ be the unique prime of $\mathbb Z[\zeta_{2n}]$ above $2$. Its additive ideal-normalized valuation is $v_{\mathfrak p}$, with $v_{\mathfrak p}(0)=+\infty$. Define $\mu(x,y)=-\min(v_{\mathfrak p}(x),v_{\mathfrak p}(y))$ and $\mu_n=v_{\mathfrak p}(1+i)$. A normalized pair has finite complexity even when a coordinate is zero. Suppose $x,y\in R_n$, $|x|^2+|y|^2=1$, and $\mu(x,y)>\mu_n$. For each integer $k$, construct
--
--   $$\begin{pmatrix}c_k\\d_k\end{pmatrix}=H_0U_z(\pi k/n)\begin{pmatrix}x\\y\end{pmatrix}.$$
--
--   Then
--
--   $$\exists k\in\mathbb Z,\qquad\mu(c_k,d_k)<\mu(x,y).$$
--
--   The gate order is $H_0U_z$, and no range restriction on $k$ is added. This is the strict descent step for column synthesis.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 22, Lemma 7.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Lemma 7.6, PDF pp.22-23. The output pair is constructed by H0*Uz and k
is an unrestricted integer. Norm preservation is not an assumed output property. -/
theorem column_complexity_reduction (n : ℕ) (hn : SmallParameter n)
    (x y : ℂ) (hx : x ∈ cyclotomicSynthesisRing n) (hy : y ∈ cyclotomicSynthesisRing n)
    (hnorm : Complex.normSq x + Complex.normSq y = 1)
    (hlarge : smallComplexity n < columnComplexity n x y) :
    ∃ k : ℤ, columnComplexity n (reducedColumn n x y k false)
      (reducedColumn n x y k true) < columnComplexity n x y := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
