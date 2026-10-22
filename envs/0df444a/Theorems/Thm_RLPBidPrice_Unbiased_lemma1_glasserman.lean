-- Prove2me | Theorems.Thm_RLPBidPrice_Unbiased_lemma1_glasserman
-- name    : RLPBidPrice.Unbiased.lemma1_glasserman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:46:05.566874+00:00
-- url     : https://prove2.me/theorems/05b03186-5113-42c0-9a51-0bd0cc00dcfb
-- title:
--   Lemma 1 (Glasserman) — d/dθ E X(θ) = E dX(θ)/dθ for a Lipschitz, a.s. differentiable random function
-- statement:
--   Let $(\Omega, P)$ be a probability space and $X(\theta) = X(\theta, \omega)$ a real random function of a real parameter $\theta$, each $X(\theta)$ a (strongly) measurable random variable, with $X(\theta_0)$ integrable. Suppose $X$ satisfies the Lipschitz condition: there is a constant $K \ge 0$ with
--   $$|X(\theta + h, \omega) - X(\theta, \omega)| \le K h \quad \text{for all } \omega,\ \theta \in \mathbb{R},\ h \ge 0,$$
--   and that $\theta \mapsto X(\theta, \omega)$ is differentiable at $\theta_0$ for $P$-almost every $\omega$. Then $\theta \mapsto \mathbb{E} X(\theta)$ is differentiable at $\theta_0$ and
--   $$\frac{d}{d\theta}\, \mathbb{E} X(\theta)\Big|_{\theta_0} = \mathbb{E}\Big[ \frac{d}{d\theta} X(\theta)\Big|_{\theta_0} \Big].$$
--
--   This is the interchange lemma the paper uses to pass from almost-sure differentiability of the LP value to differentiability of its expectation.
--
--   **Formalization Note.** The Lipschitz condition is read with $\theta$ universally quantified (a global condition; by symmetry it bounds $|X(\theta') - X(\theta)| \le K|\theta' - \theta|$). The implicit standing assumptions of "a random function" with an expectation — measurability of each $X(\theta)$ and integrability (at $\theta_0$; the Lipschitz bound then gives it everywhere) — are explicit hypotheses. The conclusion is stated with `HasDerivAt`, which asserts both that the derivative exists and that it equals the displayed expectation.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 210, Lemma 1

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

theorem lemma1_glasserman {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ) (θ₀ : ℝ)
    (hmeas : ∀ θ, AEStronglyMeasurable (X θ) P)
    (hint : Integrable (X θ₀) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ ω θ h, 0 ≤ h → |X (θ + h) ω - X θ ω| ≤ K * h)
    (hdiff : ∀ᵐ ω ∂P, DifferentiableAt ℝ (fun θ => X θ ω) θ₀) :
    HasDerivAt (fun θ => ∫ ω, X θ ω ∂P) (∫ ω, deriv (fun θ => X θ ω) θ₀ ∂P) θ₀ := by sorry

end RLPBidPrice.Unbiased
