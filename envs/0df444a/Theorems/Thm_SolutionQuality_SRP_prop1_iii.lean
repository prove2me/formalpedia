-- Prove2me | Theorems.Thm_SolutionQuality_SRP_prop1_iii
-- name    : SolutionQuality.SRP.prop1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:25.525553+00:00
-- url     : https://prove2.me/theorems/f8595805-5242-48cd-bedc-8e4e85a30680
-- title:
--   Proposition 1 (iii), p. 6 — σ²_x̂(x*_min) ≤ liminf s²_n(x*_n) ≤ limsup s²_n(x*_n) ≤ σ²_x̂(x*_max), w.p.1
-- statement:
--   Assume (A1)–(A3), let $\hat x\in X$, and let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. as $\tilde\xi$; let $x_n^*$ be optimal solutions of (SP$_n$). Let $x^*_{\min}\in\arg\min_{x\in X^*}\sigma^2_{\hat x}(x)$ and $x^*_{\max}\in\arg\max_{x\in X^*}\sigma^2_{\hat x}(x)$ be optimal solutions of (SP) with the smallest and the largest variance $\sigma^2_{\hat x}(x)=\operatorname{var}[f(\hat x,\tilde\xi)-f(x,\tilde\xi)]$. Then, with probability one,
--   $$
--   \sigma^2_{\hat x}(x^*_{\min})\le\liminf_{n\to\infty}s_n^2(x_n^*)\le\limsup_{n\to\infty}s_n^2(x_n^*)\le\sigma^2_{\hat x}(x^*_{\max}).
--   $$
--
--   The sample variance computed at the SAA minimizer is asymptotically bracketed by the smallest and largest variances over the optimal set; when $X^*$ is a singleton it is a consistent estimator of $\sigma^2_{\hat x}(x^*)$. This is the variance ingredient of the validity proofs of Theorems 2–4.
--
--   **Formalization Note.** The chain of liminf and limsup is stated in its equivalent $\varepsilon$-form, which avoids the junk value of real `liminf` on unbounded sequences: almost surely, for every $\varepsilon>0$, eventually $\sigma^2_{\hat x}(x^*_{\min})-\varepsilon\le s_n^2(x_n^*)\le\sigma^2_{\hat x}(x^*_{\max})+\varepsilon$. $x^*_{\min}$ and $x^*_{\max}$ are given points with their defining argmin/argmax properties over $X^*$.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), p. 6, Proposition 1 (iii); x*_min, x*_max defined on p. 6

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

theorem prop1_iii {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (xmin xmax : E d)
    (hxmin : xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x)
    (hxmax : xmax ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat x ≤ gapVar μ f xhat xmax) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop,
      gapVar μ f xhat xmin - ε ≤ sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ∧
        sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ≤ gapVar μ f xhat xmax + ε := by sorry

end SolutionQuality.SRP
