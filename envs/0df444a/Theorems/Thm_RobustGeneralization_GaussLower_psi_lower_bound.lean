-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_psi_lower_bound
-- name    : RobustGeneralization.GaussLower.psi_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:16:01.068542+00:00
-- url     : https://prove2.me/theorems/3ded246a-2f7f-4214-bca3-44fe097c92e7
-- title:
--   Ψ ≥ ½ 𝕀[‖µ′‖∞ ≤ ε] — every classifier has ℓ∞^ε-robust error ≥ ½ under the (m, s)-Gaussian model when ‖m‖∞ ≤ ε
-- statement:
--   Let $f : \mathbb R^d \to \{\pm 1\}$ be any classifier, $m \in \mathbb R^d$, $s > 0$ and $\varepsilon \in \mathbb R$. If $\|m\|_\infty \le \varepsilon$, then the $\ell_\infty^\varepsilon$-robust classification error of $f$ under the $(m, s)$-Gaussian model is at least one half:
--   $$\mathbb P_{(x,y) \sim P_{m,s}}\big[\exists\, x' \in \mathcal B_\infty^\varepsilon(x) : f(x') \ne y\big] \ \ge\ \tfrac12 .$$
--
--   This is the final display of the bound on $\Psi$ in the proof of Theorem 11, $\Psi \ge \frac12\,\mathbb I[\|\mu'\|_\infty \le \varepsilon]$. When $\|\mu'\|_\infty > \varepsilon$ the indicator vanishes and the bound is trivial, so the hypothesis form is equivalent. Once the adversary's budget covers the class means, no classifier does better than a coin flip.
--
--   **Formalization Note** $f$ is arbitrary: no measurability is assumed. The robust-error event contains a translate of $\{f = \mp1\}$, and translation preserves outer measure. The event probability is an outer measure (see the definitions file). $\|m\|_\infty \le \varepsilon$ is written coordinatewise. The page's $\Sigma''$ is positive definite, which is why $s > 0$ is assumed.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 29, §A.2, proof of Theorem 11, the displays from 'Now, note that as long as ‖µ′‖∞ ≤ ε' to 'Ψ ≥ … = ½ 𝕀[‖µ′‖∞ ≤ ε]'

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem psi_lower_bound {d : ℕ} (f : E d → Bool) (m : E d) (s ε : ℝ) (hs : 0 < s)
    (hm : ∀ i, |m i| ≤ ε) :
    (1 / 2 : ℝ≥0∞) ≤ robustErr (gaussModel m s) f ε := by sorry

end RobustGeneralization.GaussLower
