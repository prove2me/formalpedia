-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_eq3_posterior_predictive
-- name    : RobustGeneralization.GaussLower.eq3_posterior_predictive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:15:31.748402+00:00
-- url     : https://prove2.me/theorems/4825b4fa-fe3e-43e8-90c3-52a22c56e174
-- title:
--   Eq. (3) — averaging the (θ, σ)-Gaussian model over θ ∼ N(µ′, s²I) gives the (µ′, √(s² + σ²))-Gaussian model
-- statement:
--   Let $m \in \mathbb R^d$ and $s, \sigma > 0$. Draw $\theta \sim \mathcal N(m, s^2 I)$ and then $(x, y)$ from the $(\theta, \sigma)$-Gaussian model: $y$ is uniform on $\{\pm1\}$ and $x \sim \mathcal N(y\theta, \sigma^2 I)$. The resulting law of $(x, y)$ is the $(m, \sqrt{s^2+\sigma^2})$-Gaussian model:
--   $$\mathbb E_{\theta\sim\mathcal N(m, s^2 I)}\big[P_{\theta,\sigma}\big] = P_{m,\sqrt{s^2+\sigma^2}},$$
--   that is, $y$ uniform and $x \sim \mathcal N(y m, \Sigma'')$ with $\Sigma'' = s^2 I + \sigma^2 I$.
--
--   With $m = \mu'$ and $s^2 I = \Sigma'$ this is Equation (3) of the paper. After averaging over $\theta$, the robust error of the fixed classifier $f_n$ is its robust error under a single Gaussian model centred at the posterior mean.
--
--   **Formalization Note** The identity is stated as an equality of measures on $\mathbb R^d \times \{\pm1\}$, so it holds for every event, measurable or not. The mixture is `Measure.bind`. Standard deviations are used throughout, so $\Sigma'' = \Sigma' + \sigma^2 I$ corresponds to $\sqrt{s^2+\sigma^2}$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 29, §A.2, proof of Theorem 11, eq. (3)

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem eq3_posterior_predictive {d : ℕ} (m : E d) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ) :
    (gaussVec m s).bind (fun θ => gaussModel θ σ) =
      gaussModel m (Real.sqrt (s ^ 2 + σ ^ 2)) := by sorry

end RobustGeneralization.GaussLower
