-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_zbar_marginal
-- name    : RobustGeneralization.GaussLower.zbar_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:16:31.002592+00:00
-- url     : https://prove2.me/theorems/0ac7836c-41c5-4c48-ac1c-8e565637e107
-- title:
--   Marginal law of z̄ — the sample mean of the z_i is N(0, (1 + σ²/n) I)
-- statement:
--   Let $n \ge 1$ and $\sigma > 0$. Draw $\theta \sim \mathcal N(0, I_d)$ and then, given $\theta$, $z_1,\dots,z_n$ i.i.d. from $\mathcal N(\theta, \sigma^2 I_d)$. The sample mean $\bar z = \frac1n\sum_{i=1}^n z_i$ then has marginal law
--   $$\bar z \sim \mathcal N\Big(0, \big(1 + \tfrac{\sigma^2}{n}\big) I_d\Big).$$
--
--   Combined with $\mu' = \frac{n}{\sigma^2+n}\bar z$, this converts the bound $\Xi \ge \frac12\,\mathbb P_{\mathcal M}[\|\mu'\|_\infty \le \varepsilon]$ into a probability about a single standard Gaussian vector.
--
--   **Formalization Note** $n \ge 1$ is added because the mean of zero samples is undefined. The marginal $\mathcal M$ of $(z_1,\dots,z_n)$ is the one in the definitions file. The covariance $(1+\sigma^2/n) I$ is encoded by the standard deviation $\sqrt{1+\sigma^2/n}$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 30, §A.2, proof of Theorem 11, paragraph 'It remains to analyze the distribution of the vector z̄'

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem zbar_marginal (d n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 < σ) :
    (sampleMarginal d n σ).map (fun z => ((n : ℝ)⁻¹) • ∑ i, z i) =
      gaussVec 0 (Real.sqrt (1 + σ ^ 2 / n)) := by sorry

end RobustGeneralization.GaussLower
