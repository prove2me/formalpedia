-- Prove2me | Theorems.Thm_RankOneBTF_lemma_4
-- name    : RankOneBTF.lemma_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:22:37.776395+00:00
-- url     : https://prove2.me/theorems/5fdc4fa7-f1a9-4380-a0cc-6d3a9ebda2e6
-- title:
--   Lemma 4 — tail bound for the reciprocal of a positive random variable
-- statement:
--   Let $X$ be a positive random variable such that, for every $t\ge0$,
--   $$
--   \mathbb P\bigl[|X-\mathbb E[X]|\ge t\bigr]\le f(t)\qquad(73)
--   $$
--   for some function $f$. Then for every $s\ge0$,
--   $$
--   \mathbb P\Bigl[\Bigl|\frac1X-\frac1{\mathbb E[X]}\Bigr|\ge s\Bigr]\le f(g(s)),\qquad g(s)=\mathbb E[X]-\frac{1}{1/\mathbb E[X]+s}.\qquad(74)
--   $$
--
--   It controls the reciprocals of counts that appear in $\bar\gamma_{ijk}$ (Steps 3 and 4 of Claim 7).
--
--   **Formalization Note** The random variable is a measurable, integrable, everywhere positive real function on a probability space.
--
--   Differences from the source:
--   - reading: (73) "for some function f(·) and t ≥ 0" → (73) for every t ≥ 0; reason: the conclusion applies (73) at t = g(s), which ranges over [0, E[X]); a single t would not suffice
--   - encoding: a positive random variable with an expectation → a measurable, integrable, everywhere positive real function; reason: E[X] must exist; no instance of the lemma is lost
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.2, Lemma 4, p.31, (73)–(74)

import Mathlib

open MeasureTheory

namespace RankOneBTF

/-- **Lemma 4** (arXiv:2202.07053v3, §8.2, p.31): "Suppose that X is a positive random variable
and that we have P[|X − E[X]| ≥ t] ≤ f(t), (73) for some function f(·) and t ≥ 0. Then, for
every s ≥ 0, we have P[|1/X − 1/E[X]| ≥ s] ≤ f(g(s)), (74) where g(s) = E[X] − 1/(1/E[X] + s)."

**Formalization Note** (73) is assumed for every `t ≥ 0`. The random variable is a measurable,
integrable, everywhere positive real function on a probability space. Probabilities are
`μ.real`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : Measurable X) (hi : Integrable X μ) (hpos : ∀ ω, 0 < X ω)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ t → μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ f t)
    (s : ℝ) (hs : 0 ≤ s) :
    μ.real {ω | s ≤ |1 / X ω - 1 / ∫ ω', X ω' ∂μ|} ≤
      f ((∫ ω, X ω ∂μ) - 1 / (1 / (∫ ω, X ω ∂μ) + s)) := by sorry

end RankOneBTF
