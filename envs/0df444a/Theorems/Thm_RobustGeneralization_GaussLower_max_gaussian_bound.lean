-- Prove2me | Theorems.Thm_RobustGeneralization_GaussLower_max_gaussian_bound
-- name    : RobustGeneralization.GaussLower.max_gaussian_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:18:05.222907+00:00
-- url     : https://prove2.me/theorems/3304f4e9-2ec6-4e27-b84a-7a5a5cc87668
-- title:
--   Maximum of d Gaussians — P_{v∼N(0,I_d)}[‖v‖∞ ≤ 2√(2 log d)] ≥ 1 − 1/d
-- statement:
--   Let $d \ge 1$ and let $v \sim \mathcal N(0, I_d)$ be a standard Gaussian vector in $\mathbb R^d$. Then
--   $$\mathbb P\big[\|v\|_\infty \le 2\sqrt{2\log d}\big] \ \ge\ 1 - \frac1d .$$
--
--   This is the concentration fact for the maximum of $d$ i.i.d. standard Gaussians invoked in the proof of Corollary 23. There the paper cites Theorem 5.8 of Boucheron, Lugosi and Massart. It turns the probability in Theorem 11 into the explicit factor $1 - 1/d$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The statement is made for every natural number $d$. At $d = 0$, $1/0$ is taken as $0$ and the event is the whole space, so both sides equal $1$. At $d = 1$ the left side is $0$. $\|v\|_\infty \le r$ is written coordinatewise.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 30, §A.2, proof of Corollary 23, the sentence 'Standard concentration results for the maximum of d i.i.d. Gaussians (e.g., see Theorem 5.8 in [6]) now imply that the above probability is at least (1 − 1/d)'

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem max_gaussian_bound (d : ℕ) :
    ENNReal.ofReal (1 - 1 / (d : ℝ)) ≤
      stdGaussian (E d) {v | ∀ i, |v i| ≤ 2 * Real.sqrt (2 * Real.log d)} := by sorry

end RobustGeneralization.GaussLower
