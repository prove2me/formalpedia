-- Prove2me | Theorems.Thm_TemporalVoter_lemma_3_9
-- name    : TemporalVoter.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:10.331678+00:00
-- url     : https://prove2.me/theorems/10a38879-15bf-4c62-93ea-9d3b0facbf25
-- title:
--   Lemma 3.9 — logarithmic drift of a nonnegative integer supermartingale
-- statement:
--   Let $(X_t)$ be a supermartingale with filtration $(\mathcal F_t)$ on a probability space, taking nonnegative integer values. Fix $t\ge0$ and an event $E\in\mathcal F_t$ of positive probability on which $X_t$ equals a constant $x_t$, and suppose $\xi\ge0$ satisfies
--   $$\mathbb E\bigl[\,|X_{t+1}-x_t|\ \big|\ E\bigr]\ \ge\ \xi x_t.$$
--   Then
--   $$\mathbb E\bigl[\log(1+X_{t+1})-\log(1+X_t)\bigm|E\bigr]\ \le\ -\mathbf 1_{x_t>0}\,\frac{\xi^2}{96}.$$
--
--   A supermartingale that moves by a constant fraction of its value loses a constant amount of $\log(1+X)$ in expectation; it is applied to the embedded volume process on unstable intervals.
--
--   Differences from the source:
--   - generalization: conditioning on {F_t = F} for a possible value F of the random variable F_t generating the filtration → conditioning on any event E ∈ 𝓕_t with ℙ(E) > 0 on which X_t = x_t; reason: the proof uses only that E is in 𝓕_t (so E[X_{t+1} | E] ≤ x_t) and that X_t is constant on E; {F_t = F} is such an event
--   - encoding: non-negative integer-valued → ∀ t ω, ∃ n : ℕ, X t ω = n; reason: same condition
--   - encoding: the indicator 1_{x_t > 0} → if 0 < x then ξ²/96 else 0; reason: same value
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Lemma 3.9, p.20

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Lemma 3.9** (arXiv:2606.13374, version of 2 Nov 2026, p.20): let `(X_t)` be a nonnegative
integer-valued supermartingale with filtration `(𝓕_t)`. Fix `t ≥ 0` and an event `E ∈ 𝓕_t` of
positive probability on which `X_t = x_t`, and suppose `ξ ≥ 0` satisfies
`E[|X_{t+1} − x_t| | E] ≥ ξ x_t`. Then
`E[log(1 + X_{t+1}) − log(1 + X_t) | E] ≤ −1_{x_t > 0} ξ²/96`.

**Formalization Note** The paper conditions on `{F_t = F}` for a possible value `F` of the random
variable `F_t` generating the filtration; any event of `𝓕_t` of positive probability on which
`X_t` is constant is allowed here, which contains that case. -/
theorem lemma_3_9 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (hX : Supermartingale X ℱ P)
    (hX_nat : ∀ t ω, ∃ n : ℕ, X t ω = n) (t : ℕ) (E : Set Ω) (hE : MeasurableSet[ℱ t] E)
    (hE_pos : 0 < P E) (x : ℝ) (hx : ∀ ω ∈ E, X t ω = x) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hdev : ξ * x ≤ ∫ ω, |X (t + 1) ω - x| ∂P[|E]) :
    ∫ ω, (Real.log (1 + X (t + 1) ω) - Real.log (1 + X t ω)) ∂P[|E] ≤
      -(if 0 < x then ξ ^ 2 / 96 else 0) := by sorry

end TemporalVoter
