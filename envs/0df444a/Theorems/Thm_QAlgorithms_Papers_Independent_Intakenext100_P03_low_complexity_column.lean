-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_low_complexity_column
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.low_complexity_column
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:55:58.424323+00:00
-- url     : https://prove2.me/theorems/0427943e-618f-4e09-b076-f858afc861f6
-- title:
--   Normalized low-complexity columns are synthesizable
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   Here $n\in\{2,4,6,8,12\}$. Let $\mathfrak p$ be the unique prime of $\mathbb Z[\zeta_{2n}]$ above $2$. Its additive ideal-normalized valuation is $v_{\mathfrak p}$, with $v_{\mathfrak p}(0)=+\infty$. Define $\mu(x,y)=-\min(v_{\mathfrak p}(x),v_{\mathfrak p}(y))$ and $\mu_n=v_{\mathfrak p}(1+i)$. A normalized pair has finite complexity even when a coordinate is zero. Suppose $x,y\in R_n$, $|x|^2+|y|^2=1$, and $\mu(x,y)\le\mu_n$. Then
--
--   $$\exists V\in G_n,\qquad V\begin{pmatrix}1\\0\end{pmatrix}=\begin{pmatrix}x\\y\end{pmatrix}.$$
--
--   This is the base regime for column synthesis. The zero-coordinate cases remain included.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 20, Lemma 7.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Lemma 7.4, PDF pp.19-21. Zero coordinates remain allowed with valuation
+infinity; normalized pairs have finite complexity. The p.21 Case 3 proof
example needs cyclotomicRoot^j X instead of cyclotomicRoot^j I; the lemma itself is unchanged. -/
theorem low_complexity_column (n : ℕ) (hn : SmallParameter n)
    (x y : ℂ) (hx : x ∈ cyclotomicSynthesisRing n) (hy : y ∈ cyclotomicSynthesisRing n)
    (hnorm : Complex.normSq x + Complex.normSq y = 1)
    (hsmall : columnComplexity n x y ≤ smallComplexity n) :
    ∃ V ∈ cyclotomicGroup n, V false false = x ∧ V true false = y := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
