-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_corollary23_robust_error_lower_bound
-- name    : RobustGeneralization.GaussLower.corollary23_robust_error_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:18:37.024799+00:00
-- url     : https://prove2.me/theorems/153582e4-800e-4ab6-a2b3-583d5bb4fc85
-- title:
--   Corollary 23 — every learner's expected ℓ∞^ε-robust error is ≥ (1 − 1/d)½ when n ≤ ε²σ²/(8 log d)
-- statement:
--   Let $g_n$ be any learning algorithm, that is, a map from $n \ge 0$ samples in $\mathbb R^d \times \{\pm 1\}$ to a binary classifier $f_n$. Let $\sigma > 0$ and $\varepsilon \ge 0$. Draw $\theta \sim \mathcal N(0, I)$, then draw $n$ i.i.d. samples from the $(\theta, \sigma)$-Gaussian model, and set $f_n = g_n(\text{samples})$. If
--   $$n \ \le\ \frac{\varepsilon^2 \sigma^2}{8 \log d},$$
--   then the expected $\ell_\infty^\varepsilon$-robust classification error of $f_n$, averaged over $\theta$ and the samples, is at least
--   $$\Big(1 - \frac1d\Big)\frac12 .$$
--
--   This is the paper's lower bound for the Gaussian model. With $\sigma = c_1 d^{1/4}$, the sample size at which standard learning succeeds, robust learning needs on the order of $\varepsilon^2\sqrt d/\log d$ samples to get below error $\frac12$. That is a polynomial gap in $d$ between standard and robust generalization.
--
--   **Formalization Note** The learner is a function of the samples only, and is required to be jointly measurable in (samples, input); this is the only condition on it. $\log$ is the natural logarithm, and Lean's conventions $\log 0 = \log 1 = 0$ and $x/0 = 0$ apply. So for $d \in \{0, 1\}$ the hypothesis forces $n = 0$. The bound is then $\frac12$ at $d = 0$ (the space $\mathbb R^0$ is a point) and $0$ at $d = 1$, and both are true. The expected error is the one in the definitions file: a lower integral of outer probabilities, so a lower bound on it is the strong form.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 30, Corollary 23

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem corollary23_robust_error_lower_bound (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun q : (Fin n → E d × Bool) × E d => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hn : (n : ℝ) ≤ ε ^ 2 * σ ^ 2 / (8 * Real.log d)) :
    ENNReal.ofReal ((1 - 1 / (d : ℝ)) * (1 / 2)) ≤ expRobErr g σ ε := by sorry

end RobustGeneralization.GaussLower
