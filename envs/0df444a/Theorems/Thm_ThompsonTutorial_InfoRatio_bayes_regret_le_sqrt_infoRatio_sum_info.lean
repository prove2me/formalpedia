-- Prove2me | Theorems.Thm_ThompsonTutorial_InfoRatio_bayes_regret_le_sqrt_infoRatio_sum_info
-- name    : ThompsonTutorial.InfoRatio.bayes_regret_le_sqrt_infoRatio_sum_info
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:12:25.710109+00:00
-- url     : https://prove2.me/theorems/f9dc6784-8f4e-471e-85b8-f8a60c5fb7dc
-- title:
--   Display after (8.8): $\mathbb E[\mathrm{Regret}(T)]=\sum_t\sqrt{\Gamma_t I_t}\le\sqrt{\bar\Gamma\,T\sum_t I_t}$
-- statement:
--   **Setting.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. An unknown parameter $\theta$ takes values in a measurable space $\Theta$; noise variables $(w_t)_{t\ge1}$ in $W$ are i.i.d. and independent of $\theta$. In each period $t\ge1$ an agent picks an action $x_t$ in a standard Borel space $X$ (finite or infinite) and observes the outcome $y_t=g(x_t,\theta,w_t)$ in a standard Borel space $Y$, with reward $r(y_t)$; $g$ and $r$ are known measurable functions. The algorithm chooses $x_t=\pi_{t-1}(H_{t-1},\xi)$ by a measurable rule $\pi$ from the history $H_{t-1}=((x_1,y_1),\dots,(x_{t-1},y_{t-1}))$ and an internal randomization $\xi$ independent of $(\theta,(w_t)_{t\ge1})$. Let $\mu(x,\theta)=\mathbb E[r(g(x,\theta,w_1))\mid\theta]$ be the mean reward and let $x^*$ be a measurable random action with $x^*\in\arg\max_{x\in X}\mu(x,\theta)$. Assume each one-period regret $\mu(x^*,\theta)-\mu(x_t,\theta)$, $1\le t\le T$, is integrable. Write
--   $$
--   I_t=I\big(x^*;(x_t,y_t)\mid H_{t-1}\big),\qquad \Gamma_t=\frac{(\mathbb E[\mu(x^*,\theta)-\mu(x_t,\theta)])^2}{I_t},\qquad \bar\Gamma=\max_{1\le t\le T}\Gamma_t .
--   $$
--
--   **Statement.** If $\bar\Gamma<\infty$ and $\sum_{t=1}^T I_t<\infty$, then
--   $$
--   \mathbb E[\mathrm{Regret}(T)]=\sum_{t=1}^T\mathbb E\big[\mu(x^*,\theta)-\mu(x_t,\theta)\big]=\sum_{t=1}^T\sqrt{\Gamma_t\,I_t}\;\le\;\sqrt{\bar\Gamma\,T\sum_{t=1}^T I_t}\,.
--   $$
--   All three links are asserted. This is the analytic half of the proof of (8.8): regret is controlled by the total information gained about $x^*$, at the exchange rate $\bar\Gamma$.
--
--   **Formalization Note** Information quantities are in nats and in `ℝ≥0∞`, converted to real numbers by `toReal`; $\Gamma_t$ follows the `ℝ≥0∞` division conventions ($0/0=0$). Periods are 1-based (`Finset.Icc 1 T`).
--
--   Differences from the source:
--   - reading: actions x_t ∈ X, "finite or infinite", outcomes y_t, no structure stated → X and Y standard Borel and nonempty; reason: I(·;·|·) is defined through regular conditional distributions, which need standard Borel targets; every action and outcome set of the paper (finite sets, paths, ℝ^d, intervals) is standard Borel, and X is not restricted to be finite or countable
--   - encoding: θ, w_t random variables; g, r known functions; an adaptive rule → measurability of θ, w_t, ξ, x*, of g and π_t jointly, and of r; reason: implicit in "random variable" and in the expectations the paper writes
--   - reading: "an adaptive, possibly randomized, rule for selecting an action as a function of the history" whose randomization is "the algorithm's internal randomization" → x_t = π_{t−1}(H_{t−1}, ξ) with ξ independent of (θ, (w_t)_{t≥1}); reason: the internal randomization is the algorithm's own and carries no information about the environment
--   - generalization: µ(x, θ) = E[r(g(x, θ, w_t)) | θ] → ∫ r(g(x, θ, v)) dP_{w_1}(v), with no integrability of r∘g assumed; reason: equals the paper's µ wherever that conditional expectation exists (w_t i.i.d. and independent of θ); where it does not, Lean's µ is 0 and the statement still applies, so it specializes to the paper's claim
--   - generalization: x* ∈ argmax_x µ(x, θ), a function of θ ("x∗ = x∗(θ)", p. 76) → any measurable random action x* (a map Ω → X) with µ(a, θ) ≤ µ(x*, θ) for every a and every outcome; reason: when the argmax is not a singleton Lean's x* may break ties using other randomness; every measurable selection x*(θ) is an instance, so the statement specializes to the paper's claim
--   - encoding: E[µ(x*, θ) − µ(x_t, θ)] of a nonnegative variable, possibly +∞ → integrability of µ(x*, θ) − µ(x_t, θ) for 1 ≤ t ≤ T; reason: otherwise Γ_t = +∞ and the paper's right-hand sides are +∞ or undefined
--   - encoding: Γ̄ ∈ [0, ∞] → hypothesis Γ̄ ≠ ∞; reason: when Γ̄ = ∞ the paper's right side is +∞ or the undefined ∞·0, while in ℝ≥0∞ ⊤·0 = 0
--   - encoding: ∑_t I(x*; (x_t, y_t) | H_{t−1}) ∈ [0, ∞] → hypothesis ∑_t I_t ≠ ∞; reason: when it is infinite the paper's right side is +∞ or undefined
--   - encoding: Γ_t = 0/0 undefined when the period's expected regret and I_t both vanish → ℝ≥0∞ division (0/0 = 0, a/0 = ∞); information in nats; reason: Lean convention; the undefined case contributes 0 to every link
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), display following (8.8)

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_history
import Definitions.Def_ThompsonTutorial_InfoRatio_IsAlgorithmRun
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
import Definitions.Def_ThompsonTutorial_InfoRatio_bayesRegret
import Definitions.Def_ThompsonTutorial_InfoRatio_infoRatio
import Definitions.Def_ThompsonTutorial_InfoRatio_maxInfoRatio
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **The display following (8.8): `E[Regret(T)] = ∑ E[…] = ∑ √(Γ_t I_t) ≤ √(Γ̄ T ∑ I_t)`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), display following (8.8): "A simple argument
establishes bound (8.8): E[Regret(T)] = ∑_{t=1}^T E[μ(x∗, θ) − μ(xt, θ)]
= ∑_{t=1}^T √(Γt I(x∗; (xt, yt)|Ht−1)) ≤ √(Γ̄ T ∑_{t=1}^T I(x∗; (xt, yt)|Ht−1)), where the inequality
follows from Jensen's inequality and the fact that Γt ≤ Γ̄."

Setting (pp. 70–71, PDF 73–74): `P` is a probability measure; `θ : Ω → Θ` is the unknown parameter;
`(w_t)_{t ≥ 1}` are i.i.d. noise variables independent of `θ`; `y_t = g(x_t, θ, w_t)` with `g` and
the reward `r` known (measurable); the algorithm is a measurable rule `π` applied to the history
and an internal randomization `ξ` independent of `(θ, (w_t)_{t ≥ 1})` (`IsAlgorithmRun`);
`μ = meanReward g r (law of w_1)`; `x*` is a measurable selection of `argmax_x μ(x, θ)`. The
actions and outcomes live in standard Borel spaces, finite or infinite.

With `I_t = I(x*; (x_t, y_t) | H_{t−1})`, the conclusion is the conjunction of the three links:
(a) `E[Regret(T)] = ∑_{t=1}^T E[μ(x*, θ) − μ(x_t, θ)]`;
(b) `∑_{t=1}^T E[μ(x*, θ) − μ(x_t, θ)] = ∑_{t=1}^T √(Γ_t I_t)`;
(c) `∑_{t=1}^T √(Γ_t I_t) ≤ √(Γ̄ · T · ∑_{t=1}^T I_t)`.

**Formalization Note.** Information in nats, in `ℝ≥0∞`, converted to `ℝ` by `toReal`. The
hypotheses `hΓ : Γ̄ ≠ ⊤` and `hI : ∑ I_t ≠ ⊤` exclude exactly the cases where the paper's
right-hand sides are `+∞` (or contain `∞ · 0`); `hint` excludes the case of an infinite
one-period expected regret, where `Γ_t = +∞`. Periods are 1-based; `t − 1` is evaluated
only for `t ≥ 1`. -/
theorem bayes_regret_le_sqrt_infoRatio_sum_info
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
    (hI : (∑ t ∈ Finset.Icc 1 T, condMutualInfo P xstar (fun ω => (x t ω, y t ω))
      (history (fun s ω => (x s ω, y s ω)) (t - 1))) ≠ ⊤) :
    bayesRegret P (meanReward g r (P.map (w 1))) θ xstar x T =
        ∑ t ∈ Finset.Icc 1 T, ∫ ω, (meanReward g r (P.map (w 1)) (xstar ω) (θ ω) -
          meanReward g r (P.map (w 1)) (x t ω) (θ ω)) ∂P ∧
      ∑ t ∈ Finset.Icc 1 T, ∫ ω, (meanReward g r (P.map (w 1)) (xstar ω) (θ ω) -
          meanReward g r (P.map (w 1)) (x t ω) (θ ω)) ∂P =
        ∑ t ∈ Finset.Icc 1 T,
          Real.sqrt ((infoRatio P (meanReward g r (P.map (w 1))) θ xstar x y t).toReal *
            (condMutualInfo P xstar (fun ω => (x t ω, y t ω))
              (history (fun s ω => (x s ω, y s ω)) (t - 1))).toReal) ∧
      ∑ t ∈ Finset.Icc 1 T,
          Real.sqrt ((infoRatio P (meanReward g r (P.map (w 1))) θ xstar x y t).toReal *
            (condMutualInfo P xstar (fun ω => (x t ω, y t ω))
              (history (fun s ω => (x s ω, y s ω)) (t - 1))).toReal) ≤
        Real.sqrt ((maxInfoRatio P (meanReward g r (P.map (w 1))) θ xstar x y T).toReal * T *
          (∑ t ∈ Finset.Icc 1 T, condMutualInfo P xstar (fun ω => (x t ω, y t ω))
            (history (fun s ω => (x s ω, y s ω)) (t - 1))).toReal) := by sorry

end ThompsonTutorial.InfoRatio
