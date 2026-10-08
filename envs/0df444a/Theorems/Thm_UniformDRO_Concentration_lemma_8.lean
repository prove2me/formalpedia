-- Prove2me | Theorems.Thm_UniformDRO_Concentration_lemma_8
-- name    : UniformDRO.Concentration.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:07.538597+00:00
-- url     : https://prove2.me/theorems/9ebf5cd6-3b20-4e40-bb15-6abff3161735
-- title:
--   Lemma 8 (corrected), p. 39 — E[((1/n)Σ|Yᵢ|^{k*})^{1/k*}] ≥ E[|Y|^{k*}]^{1/k*} − (2/k)·C·n^{−1/(k*∨2)}
-- statement:
--   Let $q\in[1,\infty)$ (the paper's $k_*$; when $q>1$ it is the conjugate of $k=q/(q-1)$, so $2(q-1)/q=2/k$). Let $Y,Y_1,\dots,Y_n$ ($n\ge1$) be i.i.d. real random variables with $\mathbb E|Y|^{2q}<\infty$ and
--   $$
--   \mathbb E\big[|Y|^{2q}\big]\le C^q\,\mathbb E\big[|Y|^q\big]\qquad\text{for some }C\ge0 .
--   $$
--   Then
--   $$
--   \mathbb E\bigg[\Big(\frac1n\sum_{i=1}^n|Y_i|^q\Big)^{1/q}\bigg]\ge\mathbb E\big[|Y|^q\big]^{1/q}-\frac{2(q-1)}{q}\,C\,n^{-1/(q\vee2)} .
--   $$
--
--   Together with Jensen's inequality (which gives the reverse bound without the correction term), it shows that the plug-in $L^q$-norm is nearly unbiased; it controls the bias $|\mathbb E[g_k(\eta;\widehat P_n)]-g_k(\eta;P_0)|$ in the proof of Theorem 2.
--
--   **Formalization Note** The page (29) prints the correction as $\frac2k\sqrt C\,n^{-1/(k_*\vee2)}$. That bound is false: the hypothesis makes $C$ scale like $Y$ (replacing $Y$ by $\alpha Y$ replaces $C$ by $\alpha C$), while $\sqrt C$ scales like $\sqrt\alpha$. For instance $q=2$, $n=3$, $Y=100\cdot\mathrm{Bernoulli}(1/3)$, $C=100$ satisfies the hypothesis with equality, yet the left side is $\approx47.51$ and the printed right side is $\approx51.96$. The scaling step of the proof (App. C.1.1, p. 40) uses $C\alpha^2$ where $C\alpha$ is correct; applying the paper's own (31) to $Y/C$ gives the bound stated here with $C$ in place of $\sqrt C$. Theorem 2 is unaffected (its proof uses Lemma 8 with $C=Mc_k/(c_k-1)$, and the resulting term is the $2/k$ part of $\epsilon_t$ in (30)). The constant is written $2(q-1)/q$, since the lemma's only parameter is $q=k_*$. The law of $Y$ is a probability measure $\mu$ on $\mathbb R$ and the sample has law $\mu^{\otimes n}$; integrability of $|Y|^{2q}$ is assumed so that the moment hypothesis compares genuine expectations.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 8, eq. (29), App. C.1, p. 39; proof App. C.1.1–C.1.3, pp. 40–44 (corrected: C for √C)

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- Lemma 8 (Duchi & Namkoong, arXiv:1810.08750v6, App. C.1, p. 39, eq. (29)), corrected.
Let `q = k* ∈ [1, ∞)` and `Y₁, …, Y_n` i.i.d. with law `μ`, with
`E|Y|^{2q} ≤ C^q E|Y|^q` for some `C ≥ 0`. Then
`E[((1/n) ∑ᵢ |Yᵢ|^q)^{1/q}] ≥ E[|Y|^q]^{1/q} - 2((q - 1)/q) C n^{-1/(q ∨ 2)}`.
The page prints `(2/k)√C`; `2/k = 2(q - 1)/q` for `k = q/(q - 1)`, and `√C` is replaced by `C`
(the hypothesis makes `C` scale like `Y`, so the printed bound is false; see the NL statement).
`hint` makes `E|Y|^{2q}` a genuine expectation. -/
theorem lemma_8 (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) (hq : 1 ≤ q) (C : ℝ)
    (hC : 0 ≤ C) (hint : Integrable (fun y => |y| ^ (2 * q)) μ)
    (hmom : ∫ y, |y| ^ (2 * q) ∂μ ≤ C ^ q * ∫ y, |y| ^ q ∂μ) (n : ℕ) (hn : 0 < n) :
    (∫ y, |y| ^ q ∂μ) ^ (1 / q) - 2 * (q - 1) / q * C * (n : ℝ) ^ (-(1 / max q 2)) ≤
      ∫ ys, ((1 / n : ℝ) * ∑ i, |ys i| ^ q) ^ (1 / q) ∂(Measure.pi fun _ : Fin n => μ) := by sorry

end UniformDRO.Concentration
