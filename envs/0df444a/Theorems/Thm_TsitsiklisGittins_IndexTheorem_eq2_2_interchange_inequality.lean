-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_eq2_2_interchange_inequality
-- name    : TsitsiklisGittins.IndexTheorem.eq2_2_interchange_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:02.523739+00:00
-- url     : https://prove2.me/theorems/9aa2a703-c8fb-433d-9faa-707bfe9f4a25
-- title:
--   Equation (2.2) — the interchange inequality E[(1 − e^{−βτ})∫₀^{T(s*)} r(s*)e^{−βt}dt] ≥ E[(1 − e^{−βT(s*)})∫₀^τ r̄(t)e^{−βt}dt]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\beta>0$. Let $T\ge 0$ be a random variable (the duration $T(s^*)$ of a play at the top state $s^*$), let $\tau\in[0,\infty]$ be a random time (the first time bandit $i^*$ is played, with $\tau=\infty$ if it is never played), and let $\bar r(t)$, $t\ge 0$, be a jointly measurable bounded random reward rate with $\bar r(t)\le r(s^*)$ for all $t$. Then
--   $$
--   \mathbb E\Big[(1-e^{-\beta\tau})\int_0^{T(s^*)}r(s^*)e^{-\beta t}\,dt\Big]\ \ge\ \mathbb E\Big[(1-e^{-\beta T(s^*)})\int_0^{\tau}\bar r(t)e^{-\beta t}\,dt\Big].
--   $$
--
--   In the proof of Lemma 2.1 this inequality is equivalent to $J(\pi')\ge J(\pi)$, where $\pi'$ plays bandit $i^*$ once and then mimics the optimal policy $\pi$; it is the interchange step that makes $s^*$ a top-priority state.
--
--   **Formalization Note** $e^{-\beta\cdot\infty}=0$, and $\int_0^{\infty}$ is the integral over $(0,\infty)$; $\tau$ takes values in $[0,\infty]$. The statement uses only $\bar r(t)\le r(s^*)$, which is all the page's argument uses; no independence between $\tau$ and $T(s^*)$ is assumed. Boundedness and measurability of $\bar r$ make both expectations finite.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 196 (PDF p. 3), Section 2, proof of Lemma 2.1, equation (2.2)

import Mathlib

namespace TsitsiklisGittins.IndexTheorem

/-- Equation (2.2) of Tsitsiklis (1994), p. 196: with `τ` the (possibly infinite) first time bandit
`i*` is played, `T` the duration `T(s*)` of a play at `s*`, `r̄(t)` the reward rate under the
policy at time `t` and `r̄(t) ≤ r(s*)` for all `t`,
`E[(1 − e^{−βτ}) ∫₀^{T(s*)} r(s*) e^{−βt} dt] ≥ E[(1 − e^{−βT(s*)}) ∫₀^τ r̄(t) e^{−βt} dt]`.
Here `e^{−β·∞} = 0` and `∫₀^∞` is the integral over `(0, ∞)`. -/
theorem eq2_2_interchange_inequality {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (β : ℝ) (hβ : 0 < β)
    (T : Ω → ℝ) (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω)
    (τ : Ω → ENNReal) (hτ : Measurable τ)
    (rbar : Ω → ℝ → ℝ) (hrbar : Measurable (Function.uncurry rbar))
    (C : ℝ) (hC : ∀ ω t, |rbar ω t| ≤ C)
    (rstar : ℝ) (hle : ∀ ω t, rbar ω t ≤ rstar) :
    ∫ ω, (1 - (if τ ω = ⊤ then 0 else Real.exp (-(β * (τ ω).toReal)))) *
          (∫ t in (0 : ℝ)..T ω, rstar * Real.exp (-(β * t))) ∂P ≥
      ∫ ω, (1 - Real.exp (-(β * T ω))) *
          (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) ∂P := by sorry

end TsitsiklisGittins.IndexTheorem
