-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_lemma_C_2
-- name    : SmoothAmbEq.Gaussian.lemma_C_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:31.752224+00:00
-- url     : https://prove2.me/theorems/ce4584f1-167a-41b8-bce1-227eeaf2d0a9
-- title:
--   Lemma C.2, p. 27 — E[e^{aξ²+bξ}] and E[ξe^{aξ²+bξ}] for ξ ∼ N(µ, σ²); infinite if 2aσ² ≥ 1
-- statement:
--   Let $\xi\sim N(\mu,\sigma^2)$ with $\sigma^2\ge0$, and let $a,b\in\mathbb R$. If $2a\sigma^2<1$, then
--   $$\mathbb E\big[e^{a\xi^2+b\xi}\big]=\frac{1}{\sqrt{1-2a\sigma^2}}\exp\Big(\frac{2a\mu^2+2\mu b+b^2\sigma^2}{2(1-2a\sigma^2)}\Big)$$
--   and $\xi e^{a\xi^2+b\xi}$ is integrable with
--   $$\mathbb E\big[\xi e^{a\xi^2+b\xi}\big]=\frac{\mu+b\sigma^2}{(1-2a\sigma^2)^{3/2}}\exp\Big(\frac{2a\mu^2+2\mu b+b^2\sigma^2}{2(1-2a\sigma^2)}\Big).$$
--   If $2a\sigma^2\ge1$, then $\mathbb E[e^{a\xi^2+b\xi}]=\infty$.
--
--   These Gaussian quadratic-exponential moments drive every exponential estimate of Appendices C–G, in particular the integrability of $J$ against the Gaussian posterior.
--
--   **Formalization Note** The law is Mathlib's `gaussianReal μ v` with variance $v=\sigma^2\in\mathbb R_{\ge0}$; $v=0$ (a Dirac mass) is allowed, and the formulas hold there. The first expectation is a lower Lebesgue integral, so "$=\infty$" is meaningful; integrability of $\xi e^{a\xi^2+b\xi}$ is part of the conclusion, so the Bochner integral in the second identity is not the default value $0$.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 27, Lemma C.2

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SmoothAmbEq.Gaussian

/-- Lemma C.2, p. 27. Let `ξ ∼ N(μ, v)` with variance `v = σ² ≥ 0`. If `2av < 1`, then
`E[e^{aξ²+bξ}] = (1 - 2av)^{-1/2} e^{(2aμ²+2μb+b²v)/(2(1-2av))}` and
`E[ξ e^{aξ²+bξ}] = (μ + bv)(1 - 2av)^{-3/2} e^{(2aμ²+2μb+b²v)/(2(1-2av))}`;
if `2av ≥ 1`, then `E[e^{aξ²+bξ}] = ∞`. -/
theorem lemma_C_2 (μ a b : ℝ) (v : ℝ≥0) :
    (2 * a * v < 1 →
      (∫⁻ ξ, ENNReal.ofReal (Real.exp (a * ξ ^ 2 + b * ξ)) ∂(gaussianReal μ v)) =
          ENNReal.ofReal (1 / Real.sqrt (1 - 2 * a * v) *
            Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * v) / (2 * (1 - 2 * a * v)))) ∧
        Integrable (fun ξ => ξ * Real.exp (a * ξ ^ 2 + b * ξ)) (gaussianReal μ v) ∧
        ∫ ξ, ξ * Real.exp (a * ξ ^ 2 + b * ξ) ∂(gaussianReal μ v) =
          (μ + b * v) / (1 - 2 * a * v) ^ ((3 : ℝ) / 2) *
            Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * v) / (2 * (1 - 2 * a * v)))) ∧
    (1 ≤ 2 * a * v →
      (∫⁻ ξ, ENNReal.ofReal (Real.exp (a * ξ ^ 2 + b * ξ)) ∂(gaussianReal μ v)) = ⊤) := by sorry

end SmoothAmbEq.Gaussian
