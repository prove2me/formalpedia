-- Prove2me | Theorems.Thm_QGradGAW_Smooth_lemma_36
-- name    : QGradGAW.Smooth.lemma_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:25.84199+00:00
-- url     : https://prove2.me/theorems/c43738e9-b9d4-44a0-a40b-4af3f2c16116
-- title:
--   Lemma 36, p. 52 — ℙ[|Σ_{α∈[d]ᵏ} H_α x^α| ≥ √2 (r√(dk/2))ᵏ] ≤ 1/r^{2k} for i.i.d. symmetric x_i ∈ [−1/2, 1/2]
-- statement:
--   Let $d,k\ge1$ be integers and let $H=(H_\alpha)_{\alpha\in[d]^k}$ be an order-$k$ tensor of dimension $d$ with $|H_\alpha|\le1$ for all $\alpha$. Let $x_1,\dots,x_d$ be independent, identically distributed, symmetric real random variables with values in $[-1/2,1/2]$ and with vanishing odd moments, $\mathbb E[x_i^{2j+1}]=0$ for all $j\ge0$. Then for every $r>0$
--   $$\mathbb P\Big[\,\Big|\sum_{\alpha\in[d]^k}H_\alpha\,x^\alpha\Big|\;\ge\;\sqrt2\,\Big(r\sqrt{dk/2}\Big)^{k}\Big]\;\le\;\frac{1}{r^{2k}},\qquad x^\alpha=\prod_{j=1}^k x_{\alpha_j}.$$
--
--   This concentration bound for random multilinear forms is what produces the $\sqrt d$ (rather than $d$) scaling in Theorem 24: the $k$-th Taylor term at a random grid point is of size $(\sqrt d)^k$ rather than $d^k$.
--
--   **Formalization Note** The random variables live on a probability space $(\Omega,\mathbb P)$ and are measurable; "i.i.d." is mutual independence plus equal distributions, and "symmetric" means that $x_i$ and $-x_i$ have the same distribution. The page writes the moment condition as $\mathbb E[x_i^{2k-1}]=0$ for $k\in\mathbb N_+$, reusing the letter $k$; it is stated here with an index $j$, over the same odd exponents. The hypothesis is kept although symmetry implies it, because the page states it. $r>0$ is implicit on the page.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 52, Lemma 36

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

open MeasureTheory ProbabilityTheory

/-- arXiv:1711.00465v3, p. 52, Lemma 36: let `d, k ∈ ℕ₊`, `H ∈ (ℝ^d)^{⊗k}` with all entries in
`[−1, 1]`, and `x_1, …, x_d` i.i.d. symmetric random variables with values in `[−1/2, 1/2]` and
vanishing odd moments. Then for every `r > 0`,
`ℙ[|Σ_{α∈[d]^k} H_α x^α| ≥ √2 (r √(dk/2))^k] ≤ 1/r^{2k}`. The page's moment index (also
called `k`) is renamed `j`; `2j + 1` for `j ∈ ℕ` runs over the same odd exponents as the
page's `2k − 1`, `k ∈ ℕ₊`. -/
theorem lemma_36 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1)
    (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i j, IdentDistrib (X i) (X j) P P)
    (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) P P)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (r : ℝ) (hr : 0 < r) :
    P {ω | Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k ≤
        |∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω|} ≤ ENNReal.ofReal (1 / r ^ (2 * k)) := by sorry

end QGradGAW.Smooth
