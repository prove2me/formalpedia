-- Prove2me | Theorems.Thm_UnderstandingML_gaussian_mle
-- name    : UnderstandingML.gaussian_mle
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:33:09.134549+00:00
-- url     : https://prove2.me/theorems/4bb67880-d87c-4b94-a50a-0eadeee0856b
-- title:
--   §24.1.1: the sample mean μ̂ and σ̂ = √((1/m)∑(xᵢ − μ̂)²) maximize the Gaussian log-likelihood L(S; (μ, σ)) over μ ∈ ℝ, σ > 0
-- statement:
--   **§24.1.1 (p. 344).** For a Gaussian sample with $L(S;\theta) = -\frac1{2\sigma^2}\sum_{i=1}^m(x_i-\mu)^2 - m\log(\sigma\sqrt{2\pi})$, solving $\frac{d}{d\mu}L = 0$, $\frac{d}{d\sigma}L = 0$ gives the maximum likelihood estimates $\hat\mu = \frac1m\sum_i x_i$ and $\hat\sigma = \sqrt{\frac1m\sum_i(x_i - \hat\mu)^2}$.
--
--   Formally: $L(S;(\mu,\sigma)) \le L(S;(\hat\mu,\hat\sigma))$ for every $\mu$ and $\sigma > 0$, when $m \ge 1$ and $\hat\sigma > 0$ (for a constant sample the likelihood is unbounded).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.1.1 p. 344, the maximum likelihood estimates for a Gaussian variable

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **§24.1.1** (p. 344). For a Gaussian sample, the maximum likelihood estimates are
`μ̂ = (1/m) ∑ᵢ xᵢ` and `σ̂ = √((1/m) ∑ᵢ (xᵢ − μ̂)²)`: `L(S; (μ, σ)) ≤ L(S; (μ̂, σ̂))` for every `μ`
and every `σ > 0`. `m ≥ 1` and the sample is not constant (`σ̂ > 0`), otherwise the
likelihood is unbounded. -/
theorem gaussian_mle {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (hσ : 0 < sampleStd x) (μ σ : ℝ)
    (hσpos : 0 < σ) :
    gaussianLogLik x μ σ ≤ gaussianLogLik x (sampleMean x) (sampleStd x) := by sorry

end UnderstandingML
