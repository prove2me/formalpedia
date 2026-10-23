-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_lemma_3
-- name    : SpeedFactory.BreakEven.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:27.145697+00:00
-- url     : https://prove2.me/theorems/1ba09c45-9f0f-4a5d-9f21-0f817dd20ffa
-- title:
--   Lemma 3 (Tsypkin), p. 32 — an iid input through a linear filter g has long-run output variance σ²_x Σ g_t²
-- statement:
--   Let $(x_t)_{t\ge0}$ be independent, identically distributed real random variables with finite variance $\sigma_x^2$. Let $(g_t)_{t\ge0}$ be a real impulse response with $\sum_t g_t^2<\infty$. Define the output of the linear system by the convolution (52),
--   $$y_t=\sum_{i=0}^{t}x_i\,g_{t-i}.$$
--   Then for every $t$, $\operatorname{Var}(y_t)=\sigma_x^2\sum_{i=0}^{t}g_i^2$, and the long-run variance of the output is
--   $$\sigma_y^2=\lim_{t\to\infty}\operatorname{Var}(y_t)=\sigma_x^2\sum_{t=0}^{\infty}g_t^2 .$$
--
--   This relation is how the paper turns impulse responses into the inventory and order variances of its linear policies.
--
--   **Formalization Note** Square-summability of $g$ is added: without it the long-run variance is infinite. "Long-run variance" is read as the limit of $\operatorname{Var}(y_t)$, as in the first line of the printed proof.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 32, Lemma 3, (52), (54)

import Mathlib

open MeasureTheory ProbabilityTheory Filter

namespace SpeedFactory.BreakEven

/-- Lemma 3 (Tsypkin [1964]). Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 32, Lemma 3, (52) and (54).

If the input `x_t` of a linear system with impulse response `g_t` is iid with variance
`σ²_x`, the output `y_t = Σ_{i=0}^{t} x_i g_{t−i}` (52) has variance
`σ²_x Σ_{i=0}^{t} g_i²` at every `t`, and its long-run variance is `σ²_y = σ²_x Σ_{t=0}^∞ g_t²`
(54).

**Formalization Note.** "Long-run variance" is `lim_{t→∞} Var(y_t)` (the first line of the
printed proof). Square-summability of `g` is an added hypothesis: without it the long-run
variance is `+∞` and `tsum` would be a junk `0`. The input has a finite second moment
(`MemLp 2`), which "variance `σ²_x`" presupposes. The finite-`t` identity is the proof's
middle line. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (hind : iIndepFun x P) (hid : ∀ t, IdentDistrib (x t) (x 0) P P)
    (hL2 : MemLp (x 0) 2 P) (σx2 : ℝ) (hσx2 : variance (x 0) P = σx2)
    (g : ℕ → ℝ) (hg : Summable fun t => g t ^ 2) :
    let y : ℕ → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range (t + 1), x i ω * g (t - i)
    (∀ t, variance (y t) P = σx2 * ∑ i ∈ Finset.range (t + 1), g i ^ 2) ∧
      Tendsto (fun t => variance (y t) P) atTop (nhds (σx2 * ∑' t, g t ^ 2)) := by sorry

end SpeedFactory.BreakEven
