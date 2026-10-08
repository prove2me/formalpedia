-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_theorem_2
-- name    : RobbinsMonroSA.Conv.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:13:29.560962+00:00
-- url     : https://prove2.me/theorems/c1692779-cdc1-4c0f-8de1-80a0e2a95408
-- title:
--   Theorem 2, p. 405 — steps of type 1/n, (4), M nondecreasing with M(θ) = α and M′(θ) > 0 imply E(x_n − θ)² → 0
-- statement:
--   Let $H(y\mid x)$ be the distribution functions of the responses $Y(x)$, with regression function $M(x) = \int y\,dH(y\mid x)$, and suppose that there is a constant $C > 0$ with
--   $$\Pr[|Y(x)| \le C] = 1 \quad\text{for all } x. \tag{4}$$
--   Let $\{a_n\}$ be a sequence of type $1/n$: positive constants with $\sum a_n^2 < \infty$ and $\sum_{n\ge 2} a_n/(a_1+\cdots+a_{n-1}) = \infty$. Suppose that $M$ is nondecreasing, $M(\theta) = \alpha$ and $M'(\theta) > 0$. Let $x_1$ be an arbitrary constant and
--   $$x_{n+1} - x_n = a_n(\alpha - y_n), \qquad \Pr[y_n \le y \mid x_n] = H(y \mid x_n).$$
--   Then
--   $$\lim_{n\to\infty} E(x_n - \theta)^2 = 0.$$
--
--   This is the main theorem of Robbins and Monro (1951): the stochastic approximation iterates converge in mean square to the root $\theta$ of $M(x) = \alpha$, no matter what the initial value $x_1$.
--
--   **Formalization Note** Indices are 0-based (`x 0` is $x_1$). $H$ is a Markov kernel (`IsMarkovKernel`); (8) is the joint-law equation of the process (see the Setting definition). Condition (5) follows from (33)–(34) and (6) is part of "type $1/n$", so neither is a separate hypothesis. $M'(\theta) > 0$ is `HasDerivAt (regressionFn H) M' θ` with `0 < M'`. No Markov property beyond (8) is assumed.
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 405, Theorem 2

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- Theorem 2, p. 405. If `{a_n}` is of type `1/n`, if (4) holds, and if `M(x)` satisfies
(33) nondecreasing, (34) `M(θ) = α` and (35) `M′(θ) > 0`, then `lim b_n = 0`, whatever `x₁`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (ha : IsTypeOneOverN a) (h33 : Monotone (regressionFn H)) (h34 : regressionFn H θ = α)
    (M' : ℝ) (h35 : HasDerivAt (regressionFn H) M' θ) (h35pos : 0 < M') :
    Tendsto (fun n => msd P x θ n) atTop (𝓝 0) := by sorry

end RobbinsMonroSA.Conv
