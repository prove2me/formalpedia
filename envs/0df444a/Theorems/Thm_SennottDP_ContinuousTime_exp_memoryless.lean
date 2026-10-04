-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_exp_memoryless
-- name    : SennottDP.ContinuousTime.exp_memoryless
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T10:58:38.513676+00:00
-- url     : https://prove2.me/theorems/ce904f8a-b833-47c8-a7b6-f7bf72fbdbda
-- title:
--   Proposition 10.1.2 — the exponential distribution is memoryless and P(X ≤ δ) = μδ + o(δ)
-- statement:
--   Let $X$ be a random variable on a probability space with the exponential distribution of rate $\mu>0$, that is $P(X\le t)=1-e^{-\mu t}$ for $t\ge0$. Then
--
--   1. for all $x,y>0$,
--   $$P(X>x+y\mid X>y)=P(X>x);$$
--   2. as $\delta\to0^+$,
--   $$P(X\le\delta)=\mu\delta+o(\delta),$$
--   that is, $\big(P(X\le\delta)-\mu\delta\big)/\delta\to0$.
--
--   The first property says that an exponential service that has lasted $y$ units gives no credit for the service already rendered; the second says that a completion in a short interval has probability approximately proportional to its length. Both underlie the construction of continuous time Markov decision chains.
--
--   **Formalization Note** The law of $X$ is Mathlib's `expMeasure μ` (the image measure of $X$), and $X$ is measurable. The little-$o$ statement is `Asymptotics.IsLittleO` along the right neighbourhood filter `𝓝[>] 0`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 238, Proposition 10.1.2, eqs. (10.1)–(10.3), Definition 10.1.1

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace SennottDP.ContinuousTime

/-- Proposition 10.1.2 (p. 238). -/
theorem exp_memoryless {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ) (hX : Measurable X) (hlaw : P.map X = expMeasure μ) :
    (∀ x y : ℝ, 0 < x → 0 < y →
        P[|{ω | y < X ω}] {ω | x + y < X ω} = P {ω | x < X ω}) ∧
      (fun δ : ℝ => (P {ω | X ω ≤ δ}).toReal - μ * δ) =o[𝓝[>] (0 : ℝ)] (fun δ : ℝ => δ) := by sorry

end SennottDP.ContinuousTime
