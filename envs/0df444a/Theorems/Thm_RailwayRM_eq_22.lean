-- Prove2me | Theorems.Thm_RailwayRM_eq_22
-- name    : RailwayRM.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:37.970835+00:00
-- url     : https://prove2.me/theorems/aa2f8ace-9f79-4b15-948c-3c19c848dee8
-- title:
--   Inequality (22): $E[(W-a)^+]\le\frac12\sigma+(\mu-a)^+$
-- statement:
--   Let $W$ be a real random variable with mean $\mu$ and finite variance $\sigma^2$. Then for every real $a$,
--   $$\mathbb E\big[(W-a)^+\big]\le\tfrac12\sigma+(\mu-a)^+.$$
--
--   This distribution-free bound controls the expected number of standing passengers on a leg in terms of the first two moments of the unreserved demand.
--
--   **Formalization Note.** Finite variance is `MemLp W 2 P`.
--
--   Differences from the source:
--   - encoding: a random variable with mean μ and variance σ² → MemLp W 2 P on a probability space; reason: Mathlib's variance is 0 when the variance is infinite, so finiteness is stated
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (22), App. p. 5, PDF p. 37

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RailwayRM

/-- **(22)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (22), App. p. 5, PDF p. 37; see Gallego
and Moon 1993): for a random variable `W` with mean `μ` and variance `σ²`,
`E[(W - a)⁺] ≤ ½ σ + (μ - a)⁺` for any real `a`.

**Formalization Note.** "With variance `σ²`" is `MemLp W 2 P`: Mathlib's `variance` is `0` for a
random variable of infinite variance. -/
theorem eq_22 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : MemLp W 2 P) (a : ℝ) :
    ∫ ω, max (W ω - a) 0 ∂P ≤ Real.sqrt (variance W P) / 2 + max ((∫ ω, W ω ∂P) - a) 0 := by sorry

end RailwayRM
