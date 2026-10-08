-- Prove2me | Theorems.Thm_SolutionQuality_SRP_theorem2_srp_valid
-- name    : SolutionQuality.SRP.theorem2_srp_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:41.546472+00:00
-- url     : https://prove2.me/theorems/946a83c1-d787-4ed9-86b8-59608b964504
-- title:
--   Theorem 2, p. 7 — liminf_n P(μ_x̂ ≤ G_n(x̂) + z_α s_n(x*_n)/√n) ≥ 1 − α for the SRP (needs σ²_x̂(x*_max) > 0 when α > 1/2)
-- statement:
--   Consider the stochastic program $z^*=\min_{x\in X}Ef(x,\tilde\xi)$ under assumptions (A1)–(A3), a candidate solution $\hat x\in X$ with optimality gap $\mu_{\hat x}=Ef(\hat x,\tilde\xi)-z^*$, and observations $\tilde\xi^1,\tilde\xi^2,\dots$ i.i.d. as $\tilde\xi$. The **single replication procedure** (SRP) solves the sampled problem (SP$_n$) once, obtaining an optimal solution $x_n^*$, and computes
--   1. the gap estimate $G_n(\hat x)=\bar f_n(\hat x)-\min_{x\in X}\bar f_n(x)$ of (2), with $\bar f_n(x)=\frac1n\sum_{i=1}^n f(x,\tilde\xi^i)$;
--   2. the sample variance $s_n^2(x_n^*)=\frac1{n-1}\sum_{i=1}^n\big[(f(\hat x,\tilde\xi^i)-f(x_n^*,\tilde\xi^i))-(\bar f_n(\hat x)-\bar f_n(x_n^*))\big]^2$.
--
--   Given $0<\alpha<1$ and $z_\alpha$ with $P(N(0,1)\le z_\alpha)=1-\alpha$, the one-sided interval $[0,\,G_n(\hat x)+z_\alpha s_n(x_n^*)/\sqrt n]$ of (5) is asymptotically valid:
--   $$
--   \liminf_{n\to\infty}P\left(\mu_{\hat x}\le G_n(\hat x)+\frac{z_\alpha s_n(x_n^*)}{\sqrt n}\right)\ge1-\alpha. \qquad (6)
--   $$
--
--   The theorem shows that a single sample-average problem gives enough information for a valid statistical upper bound on the optimality gap of a candidate solution, even though $G_n(\hat x)$ need not be asymptotically normal.
--
--   **Formalization Note.** The decision dimension is $d$; the sample is the first $n$ terms `ξ 0, …, ξ (n-1)` of one i.i.d. sequence. $x_n^*$ is a measurable map that, almost surely, minimizes $\bar f_n$ over $X$ on the same sample. $f(x,\cdot)$ is measurable for each $x$, and (A2) is read as the existence of an integrable majorant of $\sup_{x\in X}f^2(x,\cdot)$. $z_\alpha$ is any real with `cdf (gaussianReal 0 1) zα = 1 - α`. Probabilities are in `ℝ≥0∞`, where `liminf` is genuine. At $n\le1$ the factors $1/n$, $1/(n-1)$ and $1/\sqrt n$ take Lean's junk value $0$, which a liminf ignores.
--
--   **Correction of the page.** The statement carries one hypothesis the page does not print: $\alpha\le 1/2$, or $\sigma^2_{\hat x}(x)>0$ for some $x\in X^*$ (equivalently $\sigma^2_{\hat x}(x^*_{\max})>0$). The page's proof of the case $\alpha>1/2$ replaces $x^*_{\min}$ by $x^*_{\max}$ and fails when $\sigma^2_{\hat x}\equiv0$ on $X^*$, where (6) itself is false: for $X=[-1,1]$, $f(x,\xi)=x^2-2x\xi$, $\tilde\xi\sim N(0,1)$, $\hat x=0$ and $\alpha=0.9$ one has $G_n(\hat x)=\bar\xi_n^2$, $s_n(x_n^*)\approx2|\bar\xi_n|$, and the coverage tends to $P(|N(0,1)|\ge 2|z_{0.9}|)\approx0.010<0.1$.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), p. 7, Theorem 2, (6); SRP and (5) on pp. 5–6

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

/-- Theorem 2 (p. 7), display (6), with the one correction recorded in the moderation:
the hypothesis `hdeg` (`α ≤ 1/2`, or some optimal `x` has `σ²_x̂(x) > 0`, i.e.
`σ²_x̂(x*_max) > 0`). The page states (6) for every `0 < α < 1`, but its proof of the case
`α > 1/2` ("replace `x*_min` with `x*_max`") breaks down when `σ²_x̂ ≡ 0` on `X*`, and (6) is
then false: `X = [-1, 1]`, `f(x, ξ) = x² - 2xξ`, `ξ̃ ~ N(0, 1)`, `x̂ = 0`, `α = 0.9` gives
coverage `→ P(|N(0,1)| ≥ 2·z_{0.1}) ≈ 0.010 < 0.1`. -/
theorem theorem2_srp_valid {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zα : ℝ) (hzα : cdf (gaussianReal 0 1) zα = 1 - α)
    (hdeg : α ≤ 1 / 2 ∨ ∃ x ∈ optSet μ f X, 0 < gapVar μ f xhat x) :
    ENNReal.ofReal (1 - α) ≤
      liminf (fun n : ℕ => P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n}) atTop := by sorry

end SolutionQuality.SRP
