-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_3
-- name    : SemiBanditSOO.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:57:58.281469+00:00
-- url     : https://prove2.me/theorems/a259d7be-97bf-4288-acb6-550cda969390
-- title:
--   Lemma 5.3 — $\int_0^1\sqrt{p_y(1-p_y)}\,dy\le\eta+\sqrt{\mathrm{Var}(Z)\log(1/\eta)}$
-- statement:
--   Let $Z\in[0,1]$ be a random variable, and define $p_y=\mathbb P(Z>y)$. For every $\eta\in(0,1)$,
--   $$\int_0^1\sqrt{p_y(1-p_y)}\,dy\le\eta+\sqrt{\mathrm{Var}(Z)\log(1/\eta)}. \qquad (5.2)$$
--
--   The integral arises when a function is written through its superlevel sets; the lemma converts the interval bounds of the confidence sets into a variance-dependent bound on expectations (Lemma 5.4(b)).
--
--   **Formalization Note.** A random variable is a measurable function on a probability space, with values in $[0,1]$.
--
--   Differences from the source: none.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.3, (5.2), p.21

import Mathlib

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.3 (superlevel-set integral versus variance).** Harada, Kawase, Sumita, *Beyond
Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1,
Lemma 5.3, (5.2), p.21.

Let `Z ∈ [0, 1]` be a random variable, and define `p_y = ℙ(Z > y)`. For every `η ∈ (0, 1)`,
`∫_0^1 √(p_y (1 − p_y)) dy ≤ η + √(Var(Z) log(1/η))`.

**Formalization Note.** A random variable is a measurable map on a probability space. -/
theorem lemma_5_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZ01 : ∀ ω, Z ω ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∫ y in (0 : ℝ)..1, Real.sqrt (μ.real {ω | y < Z ω} * (1 - μ.real {ω | y < Z ω})) ≤
      η + Real.sqrt (ProbabilityTheory.variance Z μ * Real.log (1 / η)) := by sorry

end SemiBanditSOO
