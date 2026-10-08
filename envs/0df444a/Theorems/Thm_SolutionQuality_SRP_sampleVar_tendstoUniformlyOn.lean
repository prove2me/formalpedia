-- Prove2me | Theorems.Thm_SolutionQuality_SRP_sampleVar_tendstoUniformlyOn
-- name    : SolutionQuality.SRP.sampleVar_tendstoUniformlyOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:25.636551+00:00
-- url     : https://prove2.me/theorems/68d9c73a-64f5-41ac-97aa-e90a9e2a67c8
-- title:
--   Proof of Proposition 1, pp. 6–7 — s²_n(x) → σ²_x̂(x) uniformly on X, w.p.1
-- statement:
--   Assume (A1)–(A3), let $\hat x\in X$, and let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. as $\tilde\xi$. For $x\in X$ let
--   $$
--   s_n^2(x)=\frac{1}{n-1}\sum_{i=1}^n\Big[\big(f(\hat x,\tilde\xi^i)-f(x,\tilde\xi^i)\big)-\big(\bar f_n(\hat x)-\bar f_n(x)\big)\Big]^2
--   $$
--   be the sample variance of the differences $f(\hat x,\tilde\xi^i)-f(x,\tilde\xi^i)$, and $\sigma^2_{\hat x}(x)=\operatorname{var}[f(\hat x,\tilde\xi)-f(x,\tilde\xi)]$. Then, with probability one,
--   $$
--   \sup_{x\in X}\big|s_n^2(x)-\sigma^2_{\hat x}(x)\big|\xrightarrow[n\to\infty]{}0 .
--   $$
--
--   This is the first step of the proof of Proposition 1 (iii): combined with part (ii) it controls the sample variance evaluated at the random minimizer $x_n^*$.
--
--   **Formalization Note.** The minimizers $x_n^*$ do not appear. $f(x,\cdot)$ is assumed measurable for each $x$. $\sigma^2_{\hat x}$ is Mathlib's `variance`, finite under (A2).
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), pp. 6–7, proof of Proposition 1 (iii), first claim

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

theorem sampleVar_tendstoUniformlyOn {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n x => sampleVar f xhat (fun i => ξ i ω) n x)
      (gapVar μ f xhat) atTop X := by sorry

end SolutionQuality.SRP
