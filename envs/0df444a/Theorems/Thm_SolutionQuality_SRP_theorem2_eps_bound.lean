-- Prove2me | Theorems.Thm_SolutionQuality_SRP_theorem2_eps_bound
-- name    : SolutionQuality.SRP.theorem2_eps_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:47.030353+00:00
-- url     : https://prove2.me/theorems/40ee7dec-ff69-4288-a616-3ff12b5f0410
-- title:
--   Proof of Theorem 2, p. 8 — liminf_n P(μ_x̂ ≤ G_n(x̂) + z_α s_n(x*_n)/√n) ≥ Φ((1 − ε)z_α) when α ≤ 1/2
-- statement:
--   Assume (A1)–(A3), let $\hat x\in X$, let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. as $\tilde\xi$, and let $x_n^*$ be optimal solutions of (SP$_n$). Let $0<\alpha\le 1/2$ and let $z_\alpha$ satisfy $P(N(0,1)\le z_\alpha)=1-\alpha$. Let $x^*_{\min}\in\arg\min_{x\in X^*}\sigma^2_{\hat x}(x)$ and assume $\sigma^2_{\hat x}(x^*_{\min})>0$. Then for every $0<\varepsilon<1$,
--   $$
--   \liminf_{n\to\infty}P\left(\mu_{\hat x}\le G_n(\hat x)+\frac{z_\alpha s_n(x_n^*)}{\sqrt n}\right)\ge\Phi\big((1-\varepsilon)z_\alpha\big),
--   $$
--   where $\Phi$ is the standard normal distribution function, $\mu_{\hat x}=Ef(\hat x,\tilde\xi)-z^*$ is the optimality gap, $G_n(\hat x)$ is the gap estimator (2) and $s_n(x_n^*)=\sqrt{s_n^2(x_n^*)}$.
--
--   This is the central estimate of the proof of Theorem 2; letting $\varepsilon\downarrow0$ gives the coverage bound $1-\alpha$ in the case $\alpha\le1/2$.
--
--   **Formalization Note.** The proof's "suppose $\hat x\notin X^*$" is not a hypothesis: it is implied by $\sigma^2_{\hat x}(x^*_{\min})>0$ (if $\hat x\in X^*$ then $\sigma^2_{\hat x}(\hat x)=0$ is the minimum). $z_\alpha$ is any real with `cdf (gaussianReal 0 1) zα = 1 - α`. Probabilities are in $[0,\infty]$ (`ℝ≥0∞`), where `liminf` has no junk value; $\Phi((1-\varepsilon)z_\alpha)$ enters through `ENNReal.ofReal`.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), pp. 7–8, proof of Theorem 2, (7)–(9) and the display after (9)

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

theorem theorem2_eps_bound {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zα : ℝ) (hzα : cdf (gaussianReal 0 1) zα = 1 - α)
    (xmin : E d)
    (hxmin : xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x)
    (hσ : 0 < gapVar μ f xhat xmin) (hαhalf : α ≤ 1 / 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal (cdf (gaussianReal 0 1) ((1 - ε) * zα)) ≤
      liminf (fun n : ℕ => P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n}) atTop := by sorry

end SolutionQuality.SRP
