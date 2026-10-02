-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_exp_race
-- name    : SennottDP.ContinuousTime.exp_race
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T11:01:58.423636+00:00
-- url     : https://prove2.me/theorems/e150656c-015b-4f7b-858c-f1e301e6bb94
-- title:
--   Proposition 10.1.3 — two independent exponential clocks
-- statement:
--   Let $X_1$ and $X_2$ be independent random variables, exponentially distributed with rates $\mu_1>0$ and $\mu_2>0$. Then
--
--   1. as $\delta\to0^+$, $P(X_1\le\delta,\ X_2\le\delta)=o(\delta)$;
--   2. $$P(X_1<X_2)=\frac{\mu_1}{\mu_1+\mu_2};$$
--   3. $Y=\min(X_1,X_2)$ is exponentially distributed with rate $\mu_1+\mu_2$.
--
--   These facts give the transition rates and probabilities of a continuous time chain driven by competing exponential clocks, such as arrivals and service completions in the M/M/1 queue.
--
--   **Formalization Note** The laws are Mathlib's `expMeasure`, the variables are measurable and independent (`IndepFun`), and the little-$o$ statement is taken along `𝓝[>] 0`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 239–240, Proposition 10.1.3, eqs. (10.6)–(10.7)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace SennottDP.ContinuousTime

/-- Proposition 10.1.3 (pp. 239–240). -/
theorem exp_race {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → ℝ) (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hlaw₁ : P.map X₁ = expMeasure μ₁) (hlaw₂ : P.map X₂ = expMeasure μ₂)
    (hindep : IndepFun X₁ X₂ P) :
    (fun δ : ℝ => (P {ω | X₁ ω ≤ δ ∧ X₂ ω ≤ δ}).toReal) =o[𝓝[>] (0 : ℝ)] (fun δ : ℝ => δ) ∧
      P {ω | X₁ ω < X₂ ω} = ENNReal.ofReal (μ₁ / (μ₁ + μ₂)) ∧
      P.map (fun ω => min (X₁ ω) (X₂ ω)) = expMeasure (μ₁ + μ₂) := by sorry

end SennottDP.ContinuousTime
