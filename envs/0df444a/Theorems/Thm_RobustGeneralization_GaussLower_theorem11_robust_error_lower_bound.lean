-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_theorem11_robust_error_lower_bound
-- name    : RobustGeneralization.GaussLower.theorem11_robust_error_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:17:28.673492+00:00
-- url     : https://prove2.me/theorems/c730cccd-81a4-41f5-8af2-33a054cfa676
-- title:
--   Theorem 11 — every learner's expected ℓ∞^ε-robust error is ≥ ½ P_{v∼N(0,I)}[√(n/(σ²+n)) ‖v‖∞ ≤ ε]
-- statement:
--   Let $g_n$ be any learning algorithm, that is, a map from $n$ samples in $\mathbb R^d \times \{\pm1\}$ to a binary classifier $f_n$. Let $\sigma > 0$ and $\varepsilon \ge 0$. Draw $\theta \sim \mathcal N(0, I)$, then draw $n$ i.i.d. samples from the $(\theta, \sigma)$-Gaussian model, and set $f_n = g_n(\text{samples})$. Then the expected $\ell_\infty^\varepsilon$-robust classification error of $f_n$, averaged over $\theta$ and the samples, satisfies
--   $$\Xi \ \ge\ \frac12\ \mathbb P_{v \sim \mathcal N(0, I)}\Big[\sqrt{\tfrac{n}{\sigma^2 + n}}\ \|v\|_\infty \le \varepsilon\Big].$$
--
--   The bound holds for every learner, however it uses the data. It is the paper's information-theoretic lower bound for robust learning in the Gaussian model. Corollary 23 turns it into an explicit sample-size threshold.
--
--   **Formalization Note** The learner is a function of the samples only, and is required to be jointly measurable in (samples, input). This is the only condition on $g_n$; it is needed for the expectation over the samples to be the paper's expectation. The expectation $\Xi$ is a lower Lebesgue integral of outer probabilities (see the definitions file), so a lower bound on it is the strong form. $\sqrt{n/(\sigma^2+n)}\,\|v\|_\infty \le \varepsilon$ is written coordinatewise as $\sqrt{n/(\sigma^2+n)}\,|v_i| \le \varepsilon$ for all $i$, which is equivalent because $\varepsilon \ge 0$. At $n = 0$ the right-hand side is $\frac12$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 28, Theorem 11 (also p. 8, §3, Theorem 11)

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem theorem11_robust_error_lower_bound (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun q : (Fin n → E d × Bool) × E d => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (1 / 2 : ℝ≥0∞) *
        stdGaussian (E d) {v | ∀ i, Real.sqrt (n / (σ ^ 2 + n)) * |v i| ≤ ε} ≤
      expRobErr g σ ε := by sorry

end RobustGeneralization.GaussLower
