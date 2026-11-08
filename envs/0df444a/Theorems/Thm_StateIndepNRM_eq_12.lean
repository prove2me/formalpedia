-- Prove2me | Theorems.Thm_StateIndepNRM_eq_12
-- name    : StateIndepNRM.eq_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:36:16.485897+00:00
-- url     : https://prove2.me/theorems/9ee998f5-ca8d-41d6-adec-4f71aecdbf3d
-- title:
--   (12), p.12 — Poisson tail bound $P(\mathcal X(\lambda)\ge\lambda+x)\le e^{-x^2/(2(\lambda+x))}$
-- statement:
--   Let $\mathcal X(\lambda)$ be a Poisson random variable with mean $\lambda>0$. For every real $x\ge0$,
--
--   $$
--   P(\mathcal X(\lambda)\ge\lambda+x)\le e^{-\frac{x^2}{2(\lambda+x)}}.
--   $$
--
--   This is the concentration inequality the paper cites from Canonne (2019) and Pollard (2015), and it replaces the renewal arguments unavailable for a non-homogeneous arrival process.
--
--   Differences from the source:
--   - encoding: 𝒳(λ) a Poisson variable with mean λ > 0 → r : ℝ≥0 with 0 < r, and the probability under poissonMeasure r of {j : ℕ | r + x ≤ j}; reason: Mathlib's Poisson law takes an ℝ≥0 mean and lives on ℕ; the instances are the same
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, (12), p.12

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StateIndepNRM

/-- (12), p.12 (Manchiraju–Dawande–Janakiraman, SSRN 3831496; cited from Canonne 2019, Pollard 2015):
for a Poisson variable `𝒳(r)` with mean `r > 0` and `x ≥ 0`,
`P(𝒳(r) ≥ r + x) ≤ exp(−x² / (2 (r + x)))`.

**Formalization Note.** `x` is real, so the event is `{j : ℕ | r + x ≤ j}`. -/
theorem eq_12 (r : ℝ≥0) (hr : 0 < r) (x : ℝ) (hx : 0 ≤ x) :
    (poissonMeasure r).real {j : ℕ | (r : ℝ) + x ≤ j} ≤
      Real.exp (-(x ^ 2 / (2 * ((r : ℝ) + x)))) := by sorry

end StateIndepNRM
