-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_eq2_posterior_swap
-- name    : RobustGeneralization.GaussLower.eq2_posterior_swap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:14:55.775553+00:00
-- url     : https://prove2.me/theorems/5f2ebc8d-3199-4f64-ae1d-994e32110d4e
-- title:
--   Eq. (2) — Gaussian conjugacy: swapping the prior N(0, I) with the samples z_i ∼ N(θ, σ²I)
-- statement:
--   Let $\sigma > 0$ and $n \ge 0$. Draw $\theta \sim \mathcal N(0, I_d)$ and then, given $\theta$, $z_1, \dots, z_n$ i.i.d. from $\mathcal N(\theta, \sigma^2 I_d)$. Let $\mathcal M$ be the marginal law of $z = (z_1,\dots,z_n)$. For each $z$, let $\mathcal N(\mu'(z), \Sigma')$ be the Gaussian with
--   $$\mu'(z) = \frac{1}{\sigma^2 + n}\sum_{i=1}^n z_i,\qquad \Sigma' = \frac{\sigma^2}{\sigma^2 + n} I_d.$$
--   Then the conditional law of $\theta$ given $z$ is $\mathcal N(\mu'(z), \Sigma')$. Equivalently, for every measurable $F : \mathbb R^d \times (\mathbb R^d)^n \to [0, \infty]$,
--   $$\mathbb E_{\theta \sim \mathcal N(0,I)}\ \mathbb E_{z_1,\dots,z_n \sim \mathcal N(\theta,\sigma^2 I)}\big[F(\theta, z)\big] = \mathbb E_{z \sim \mathcal M}\ \mathbb E_{\theta \sim \mathcal N(\mu'(z), \Sigma')}\big[F(\theta, z)\big].$$
--
--   This is the step that yields Equation (2) of the paper. After it, the parameter $\theta$ is drawn after the classifier $f_n$ has been fixed by the samples.
--
--   **Formalization Note** The paper writes $\mu' = \frac{n}{\sigma^2+n}\bar z$ with "$\bar z = \sum_{i=1}^n z_i$". For $\mu'$ to be the posterior mean, $\bar z$ must be the sample mean $\frac1n\sum_i z_i$, as it is on p. 30. The statement uses $(\sigma^2+n)^{-1}\sum_i z_i$, which equals $\frac{n}{\sigma^2+n}\cdot\frac1n\sum_i z_i$ and is also defined at $n=0$. $\Sigma' = \frac{\sigma^2}{\sigma^2+n}I$ is encoded by the standard deviation $\sigma/\sqrt{\sigma^2+n}$. $\mathcal M$ is the mixture `(stdGaussian).bind` of the product laws $\mathcal N(\theta,\sigma^2 I)^{\otimes n}$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 28, §A.2, proof of Theorem 11, eq. (2) and the definitions of µ′, Σ′, M before it

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem eq2_posterior_swap (d n : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (F : E d × (Fin n → E d) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ θ, ∫⁻ z, F (θ, z) ∂(Measure.pi fun _ : Fin n => gaussVec θ σ) ∂(stdGaussian (E d)) =
      ∫⁻ z, ∫⁻ θ, F (θ, z) ∂(posterior z σ) ∂(sampleMarginal d n σ) := by sorry

end RobustGeneralization.GaussLower
