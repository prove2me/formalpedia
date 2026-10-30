-- Prove2me | Theorems.Thm_ThompsonTutorial_InfoRatio_bayes_regret_le_sqrt_infoRatio_entropy
-- name    : ThompsonTutorial.InfoRatio.bayes_regret_le_sqrt_infoRatio_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:14:43.653903+00:00
-- url     : https://prove2.me/theorems/91543ab6-1ce4-4002-b9b1-fdb4a4593103
-- title:
--   (8.8): $\mathbb E[\mathrm{Regret}(T)]\le\sqrt{\bar\Gamma\,H(x^*)\,T}$ for any model and algorithm
-- statement:
--   **Setting.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. An unknown parameter $\theta$ takes values in a measurable space $\Theta$; noise variables $(w_t)_{t\ge1}$ in $W$ are i.i.d. and independent of $\theta$. In each period $t\ge1$ an agent picks an action $x_t$ in a standard Borel space $X$ (finite or infinite) and observes the outcome $y_t=g(x_t,\theta,w_t)$ in a standard Borel space $Y$, with reward $r(y_t)$; $g$ and $r$ are known measurable functions. An algorithm is a measurable rule $\pi$ choosing $x_t=\pi_{t-1}(H_{t-1},\xi)$ from the history $H_{t-1}=((x_1,y_1),\dots,(x_{t-1},y_{t-1}))$ and an internal randomization $\xi$ independent of $(\theta,(w_t)_{t\ge1})$. Let
--   $$
--   \mu(x,\theta)=\mathbb E\big[r(g(x,\theta,w_t))\mid\theta\big]
--   $$
--   be the mean reward, and let $x^*$ be a measurable random action with $x^*\in\arg\max_{x\in X}\mu(x,\theta)$. Assume each one-period regret $\mu(x^*,\theta)-\mu(x_t,\theta)$, $1\le t\le T$, is integrable. The information ratio (8.7) of period $t$ is
--   $$
--   \Gamma_t=\frac{\big(\mathbb E[\mu(x^*,\theta)-\mu(x_t,\theta)]\big)^2}{I\big(x^*;(x_t,y_t)\mid H_{t-1}\big)},\qquad \bar\Gamma=\max_{t\in\{1,\dots,T\}}\Gamma_t ,
--   $$
--   and $H(x^*)$ is the entropy of the optimal action.
--
--   **Statement.** For every horizon $T$, if $\bar\Gamma<\infty$ and $H(x^*)<\infty$, then
--   $$
--   \mathbb E[\mathrm{Regret}(T)]\;=\;\mathbb E\Big[\sum_{t=1}^T\big(\mu(x^*,\theta)-\mu(x_t,\theta)\big)\Big]\;\le\;\sqrt{\bar\Gamma\,H(x^*)\,T}\,.
--   $$
--
--   The bound applies to any model of this form and any algorithm. Its feature is the dependence on the entropy $H(x^*)$ of the prior distribution of the optimal action, which measures initial uncertainty and can be much smaller than the logarithm of the number of actions; bounds on $\bar\Gamma$ for specific problems (for instance $d/2$ for Thompson sampling on shortest-path problems with $d$ edges) turn it into explicit regret bounds.
--
--   **Formalization Note** Information quantities are in nats and in `ℝ≥0∞`, converted to real numbers by `toReal`; $\Gamma_t$ follows the `ℝ≥0∞` division conventions. Periods are 1-based (`Finset.Icc 1 T`); at $T=0$ both sides are $0$.
--
--   Differences from the source:
--   - reading: actions x_t ∈ X, "finite or infinite", outcomes y_t, no structure stated → X and Y standard Borel and nonempty; reason: I(·;·|·) is defined through regular conditional distributions, which need standard Borel targets; every action and outcome set of the paper (finite sets, paths, ℝ^d, intervals) is standard Borel, and X is not restricted to be finite or countable
--   - encoding: θ, w_t random variables; g, r known functions; an adaptive rule → measurability of θ, w_t, ξ, x*, of g and π_t jointly, and of r; reason: implicit in "random variable" and in the expectations the paper writes
--   - reading: "an adaptive, possibly randomized, rule for selecting an action as a function of the history" whose randomization is "the algorithm's internal randomization" → x_t = π_{t−1}(H_{t−1}, ξ) with ξ independent of (θ, (w_t)_{t≥1}); reason: the internal randomization is the algorithm's own and carries no information about the environment
--   - generalization: µ(x, θ) = E[r(g(x, θ, w_t)) | θ] → ∫ r(g(x, θ, v)) dP_{w_1}(v), with no integrability of r∘g assumed; reason: equals the paper's µ wherever that conditional expectation exists (w_t i.i.d. and independent of θ); where it does not, Lean's µ is 0 and the statement still applies, so it specializes to the paper's claim
--   - generalization: x* ∈ argmax_x µ(x, θ), a function of θ ("x∗ = x∗(θ)", p. 76) → any measurable random action x* (a map Ω → X) with µ(a, θ) ≤ µ(x*, θ) for every a and every outcome; reason: when the argmax is not a singleton Lean's x* may break ties using other randomness; every measurable selection x*(θ) is an instance, so the statement specializes to the paper's claim
--   - encoding: E[µ(x*, θ) − µ(x_t, θ)] of a nonnegative variable, possibly +∞ → integrability of µ(x*, θ) − µ(x_t, θ) for 1 ≤ t ≤ T; reason: otherwise Γ_t = +∞ and the paper's right side is +∞ or undefined
--   - encoding: Γ̄ ∈ [0, ∞] → hypothesis Γ̄ ≠ ∞; reason: when Γ̄ = ∞ the paper's right side is +∞ or the undefined ∞·0, while in ℝ≥0∞ ⊤·0 = 0 would make the Lean right side 0
--   - encoding: H(x*) ∈ [0, ∞] → hypothesis H(x*) ≠ ∞; reason: when H(x*) = ∞ the paper's right side is +∞ or the undefined 0·∞, while in ℝ≥0∞ the Lean right side could be 0
--   - encoding: Γ_t = 0/0 undefined when the period's expected regret and I(x*; (x_t, y_t) | H_{t−1}) both vanish → ℝ≥0∞ division (0/0 = 0, a/0 = ∞); information in nats; reason: Lean convention; such a period contributes 0 regret
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 76 (PDF p. 79), (8.8), with the information ratio (8.7), p. 75 (PDF p. 78), and the model of §8.1.2 "Problem Formulation", pp. 70–71 (PDF pp. 73–74). Quote: "The following regret bound from (Russo and Van Roy, 2016), which applies to any model and algorithm, formalizes this observation: (8.8) E[Regret(T)] ≤ √(Γ̄ H(x∗) T), where Γ̄ = max_{t∈{1,...,T}} Γt."

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_history
import Definitions.Def_ThompsonTutorial_InfoRatio_IsAlgorithmRun
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
import Definitions.Def_ThompsonTutorial_InfoRatio_bayesRegret
import Definitions.Def_ThompsonTutorial_InfoRatio_infoRatio
import Definitions.Def_ThompsonTutorial_InfoRatio_maxInfoRatio
import Definitions.Def_ThompsonTutorial_InfoRatio_entropy
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **(8.8): Bayesian regret is at most `√(Γ̄ H(x*) T)`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), (8.8): "The following regret bound from (Russo
and Van Roy, 2016), which applies to any model and algorithm, formalizes this observation:
E[Regret(T)] ≤ √(Γ̄ H(x∗) T), where Γ̄ = max_{t∈{1,...,T}} Γt." with `Γ_t` the information
ratio (8.7), p. 75 (PDF p. 78).

Setting (pp. 70–71, PDF 73–74): `P` is a probability measure; `θ : Ω → Θ` is the unknown parameter;
`(w_t)_{t ≥ 1}` are i.i.d. noise variables independent of `θ`; `y_t = g(x_t, θ, w_t)` with `g` and
the reward `r` known (measurable); the algorithm is a measurable rule `π` applied to the history
and an internal randomization `ξ` independent of `(θ, (w_t)_{t ≥ 1})` (`IsAlgorithmRun`);
`μ = meanReward g r (law of w_1)`; `x*` is a measurable selection of `argmax_x μ(x, θ)`. The
actions and outcomes live in standard Borel spaces, finite or infinite.

Conclusion: `E[Regret(T)] ≤ √(Γ̄ · H(x*) · T)` with `Γ̄ = max_{1 ≤ t ≤ T} Γ_t`.

**Formalization Note.** Information in nats, in `ℝ≥0∞`. Hypotheses `hΓ : Γ̄ ≠ ⊤` and
`hH : H(x*) ≠ ⊤` exclude exactly the cases in which the paper's right side is `+∞` or the
undefined `∞ · 0` (in `ℝ≥0∞`, `⊤ * 0 = 0`, which would otherwise make the right side `0`).
`hint` asks the one-period regret to be integrable; it is nonnegative, so otherwise its
expectation is `+∞`, `Γ_t = +∞`, and the paper's bound is again `+∞`. Periods are 1-based. -/
theorem bayes_regret_le_sqrt_infoRatio_entropy
    {Ω X Y Θ W Ξ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Θ] [MeasurableSpace W] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : X → Θ → W → Y) (r : Y → ℝ) (θ : Ω → Θ) (w : ℕ → Ω → W) (ξ : Ω → Ξ)
    (π : (t : ℕ) → (Fin t → X × Y) → Ξ → X) (x : ℕ → Ω → X) (y : ℕ → Ω → Y)
    (xstar : Ω → X) (T : ℕ)
    (hg : Measurable (fun p : X × Θ × W => g p.1 p.2.1 p.2.2))
    (hr : Measurable r)
    (hπ : ∀ t, Measurable (fun p : (Fin t → X × Y) × Ξ => π t p.1 p.2))
    (hθ : Measurable θ) (hw : ∀ t, Measurable (w t)) (hξ : Measurable ξ)
    (hw_indep : iIndepFun (fun t : ℕ => w (t + 1)) P)
    (hw_ident : ∀ t : ℕ, IdentDistrib (w (t + 1)) (w 1) P P)
    (hθw : IndepFun θ (fun ω (t : ℕ) => w (t + 1) ω) P)
    (hξθw : IndepFun ξ (fun ω => (θ ω, fun t : ℕ => w (t + 1) ω)) P)
    (hrun : IsAlgorithmRun g θ w ξ π x y)
    (hxstar_meas : Measurable xstar)
    (hxstar : ∀ (ω : Ω) (a : X),
      meanReward g r (P.map (w 1)) a (θ ω) ≤ meanReward g r (P.map (w 1)) (xstar ω) (θ ω))
    (hint : ∀ t ∈ Finset.Icc 1 T, Integrable (fun ω =>
      meanReward g r (P.map (w 1)) (xstar ω) (θ ω) - meanReward g r (P.map (w 1)) (x t ω) (θ ω)) P)
    (hΓ : maxInfoRatio P (meanReward g r (P.map (w 1))) θ xstar x y T ≠ ⊤)
    (hH : entropy P xstar ≠ ⊤) :
    bayesRegret P (meanReward g r (P.map (w 1))) θ xstar x T ≤
      Real.sqrt ((maxInfoRatio P (meanReward g r (P.map (w 1))) θ xstar x y T).toReal *
        (entropy P xstar).toReal * T) := by sorry

end ThompsonTutorial.InfoRatio
