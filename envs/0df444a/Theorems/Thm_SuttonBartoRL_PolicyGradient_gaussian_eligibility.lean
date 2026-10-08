-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_gaussian_eligibility
-- name    : SuttonBartoRL.PolicyGradient.gaussian_eligibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:16:35.031675+00:00
-- url     : https://prove2.me/theorems/731f4360-8270-4358-86bd-d28c7c0b9f4b
-- title:
--   Exercise 13.4 — eligibility vectors of the Gaussian policy
-- statement:
--   For the Gaussian policy $\pi(a\mid s,\theta)$ with mean $\mu(s,\theta) = \theta_\mu^\top x_\mu(s)$ and standard deviation $\sigma(s,\theta) = \exp(\theta_\sigma^\top x_\sigma(s))$, and for every state $s$, real action $a$ and parameter $\theta = [\theta_\mu, \theta_\sigma]^\top$, the two parts of the eligibility vector are
--   $$
--   \nabla_{\theta_\mu} \ln \pi(a \mid s, \theta) = \frac{1}{\sigma(s,\theta)^2}\big(a - \mu(s,\theta)\big)\, x_\mu(s),
--   \qquad
--   \nabla_{\theta_\sigma} \ln \pi(a \mid s, \theta) = \Big(\frac{(a - \mu(s,\theta))^2}{\sigma(s,\theta)^2} - 1\Big)\, x_\sigma(s).
--   $$
--
--   These are the vectors used by policy-gradient methods with continuous actions.
--
--   **Formalization Note** Each part is a gradient with respect to one block of $\theta$, the other block held fixed. The book also writes each part as $\nabla\pi/\pi$; that equality is the identity $\nabla \ln x = \nabla x / x$ and is not restated.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 13.4, p. 336, with Eqs. (13.19)–(13.20), pp. 335–336

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_GaussianPolicy

namespace SuttonBartoRL.PolicyGradient

/-- Exercise 13.4, p. 336: for the Gaussian policy (13.19) with mean `µ(s, θ) = θ_µᵀ x_µ(s)` and
standard deviation `σ(s, θ) = exp(θ_σᵀ x_σ(s))` (13.20), the eligibility vector has the two parts
`∇_{θ_µ} ln π(a|s, θ) = (1/σ(s, θ)²)(a − µ(s, θ)) x_µ(s)` and
`∇_{θ_σ} ln π(a|s, θ) = ((a − µ(s, θ))²/σ(s, θ)² − 1) x_σ(s)`. -/
theorem gaussian_eligibility {S : Type} {dμ dσ : ℕ}
    (xμ : S → EuclideanSpace ℝ (Fin dμ)) (xσ : S → EuclideanSpace ℝ (Fin dσ))
    (θμ : EuclideanSpace ℝ (Fin dμ)) (θσ : EuclideanSpace ℝ (Fin dσ)) (s : S) (a : ℝ) :
    HasGradientAt (fun θμ' => Real.log (gaussianPolicy xμ xσ θμ' θσ s a))
      ((1 / gaussStd xσ θσ s ^ 2 * (a - gaussMean xμ θμ s)) • xμ s) θμ ∧
    HasGradientAt (fun θσ' => Real.log (gaussianPolicy xμ xσ θμ θσ' s a))
      (((a - gaussMean xμ θμ s) ^ 2 / gaussStd xσ θσ s ^ 2 - 1) • xσ s) θσ := by sorry

end SuttonBartoRL.PolicyGradient
