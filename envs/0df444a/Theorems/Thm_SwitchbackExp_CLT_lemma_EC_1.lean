-- Prove2me | Theorems.Thm_SwitchbackExp_CLT_lemma_EC_1
-- name    : SwitchbackExp.CLT.lemma_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:52.216096+00:00
-- url     : https://prove2.me/theorems/f63fd7d5-f15d-423a-a2fe-0540b6ab177c
-- title:
--   Lemma EC.1 (Romano–Wolf 2000, Thm 2.1), p. ec1 — CLT for triangular arrays of ϕ-dependent variables under conditions 1–5 (with d_n → ∞ and L_n > 0 added)
-- statement:
--   Let $\{X_{n,i}\}$ be a triangular array of zero-mean real random variables: for each $n$, the variables $X_{n,1},\dots,X_{n,d_n}$ live on a probability space $(\Omega_n,\mu_n)$. Let $\phi\ge1$ be a fixed integer and suppose each row $X_{n,1},\dots,X_{n,d_n}$ is $\phi$-dependent. Define
--   $$B^2_{n,k,a}=\mathrm{Var}\Big(\sum_{i=a}^{a+k-1}X_{n,i}\Big),\qquad B^2_n=B^2_{n,d_n,1}=\mathrm{Var}\Big(\sum_{i=1}^{d_n}X_{n,i}\Big).$$
--   Let $\delta>0$ and $-1\le\gamma\le1$, and let $\Delta_n$, $K_n$, $L_n>0$ be real sequences such that
--
--   1. $\mathbb E|X_{n,i}|^{2+\delta}\le\Delta_n$ for all $i$;
--   2. $B^2_{n,k,a}/k^{1+\gamma}\le K_n$ for all $a$ and all $k\ge\phi$;
--   3. $B^2_n/(d_n\phi^\gamma)\ge L_n$;
--   4. $K_n/L_n=O(1)$;
--   5. $\Delta_n/L_n^{(2+\delta)/2}=O(1)$;
--
--   and suppose $d_n\to\infty$. Then
--   $$\frac{\sum_{i=1}^{d_n}X_{n,i}}{B_n}\xrightarrow{D}\mathcal N(0,1).$$
--
--   This is the central limit theorem used to prove the asymptotic normality of the Horvitz–Thompson estimator (Theorem 3).
--
--   **Formalization Note** Two hypotheses are added to the page's statement. (i) $d_n\to\infty$: without it the statement is false (take $d_n=1$ and $X_{n,1}$ a Rademacher variable; conditions 1–5 hold with $\Delta_n=K_n=L_n=1$, but the normalised sum is $\pm1$). Romano and Wolf's Theorem 2.1 has a sixth condition $\phi^{1+(1-\gamma)(1+2/\delta)}/d_n\to0$, which for fixed $\phi$ is exactly $d_n\to\infty$. (ii) $L_n>0$: the ratios in conditions 4–5 presuppose it. Condition 1 is stated with the Lebesgue integral of $|X_{n,i}|^{2+\delta}$ in $[0,\infty]$, so it also asserts integrability; the zero mean is the Bochner integral. Condition 2 is required for windows $1\le a$, $a+k-1\le d_n$ inside the row. $O(1)$ means bounded in absolute value for all large $n$. Condition 5 reads "$\Delta/L_n^{(2+\delta)/2}$" on the page; it is $\Delta_n$. Each row is a function `X n : ℕ → Ω n → ℝ` read at indices $1,\dots,d_n$, and every row index $n\in\mathbb N$ (including $n=0$) carries the hypotheses; only the limit matters.
-- source:
--   arXiv:2009.00148v4, Lemma EC.1, p. ec1 (Romano and Wolf 2000, Statist. Probab. Lett. 47, 115–124, Theorem 2.1)

import Mathlib
import Definitions.Def_SwitchbackExp_CLT_PhiDependent

open MeasureTheory ProbabilityTheory Filter

namespace SwitchbackExp.CLT

/-- Lemma EC.1 (Romano and Wolf (2000), Theorem 2.1), p. ec1: a central limit theorem for triangular arrays
of zero-mean ϕ-dependent random variables `X_{n,1}, …, X_{n,d_n}` under the moment and variance conditions
1–5, with the added hypotheses `L_n > 0` and `d_n → ∞`. -/
theorem lemma_EC_1 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (d : ℕ → ℕ) (X : ∀ n, ℕ → Ω n → ℝ) (ϕ : ℕ) (hϕ : 1 ≤ ϕ)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ₁ : -1 ≤ γ) (hγ₂ : γ ≤ 1) (Δ K L : ℕ → ℝ)
    (hmeas : ∀ n i, 1 ≤ i → i ≤ d n → Measurable (X n i))
    (hmean : ∀ n i, 1 ≤ i → i ≤ d n → ∫ ω, X n i ω ∂(μ n) = 0)
    (hdep : ∀ n, IsPhiDependent (μ n) ϕ (d n) (X n))
    (h1 : ∀ n i, 1 ≤ i → i ≤ d n → ∫⁻ ω, ‖X n i ω‖ₑ ^ (2 + δ) ∂(μ n) ≤ ENNReal.ofReal (Δ n))
    (h2 : ∀ n a k, 1 ≤ a → ϕ ≤ k → a + k ≤ d n + 1 →
      variance (∑ i ∈ Finset.Icc a (a + k - 1), X n i) (μ n) / (k : ℝ) ^ (1 + γ) ≤ K n)
    (h3 : ∀ n, L n ≤ variance (∑ i ∈ Finset.Icc 1 (d n), X n i) (μ n) / ((d n : ℝ) * (ϕ : ℝ) ^ γ))
    (h4 : ∃ C, ∀ᶠ n in atTop, |K n / L n| ≤ C)
    (h5 : ∃ C, ∀ᶠ n in atTop, |Δ n / L n ^ ((2 + δ) / 2)| ≤ C)
    (hL : ∀ n, 0 < L n) (hd : Tendsto d atTop atTop) :
    TendstoInDistribution
      (fun n ω => (∑ i ∈ Finset.Icc 1 (d n), X n i ω) /
        Real.sqrt (variance (∑ i ∈ Finset.Icc 1 (d n), X n i) (μ n)))
      atTop id μ (gaussianReal 0 1) := by sorry

end SwitchbackExp.CLT
