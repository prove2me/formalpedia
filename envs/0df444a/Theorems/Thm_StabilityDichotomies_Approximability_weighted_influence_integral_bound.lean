-- Prove2me | Theorems.Thm_StabilityDichotomies_Approximability_weighted_influence_integral_bound
-- name    : StabilityDichotomies.Approximability.weighted_influence_integral_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:16:20.798584+00:00
-- url     : https://prove2.me/theorems/6062b1b8-1df3-41aa-9da7-fabc9738e086
-- title:
--   Weighted influence integral is bounded by total variation
-- statement:
--   Let $\varepsilon\ge0$, and suppose $F$ has an integrable, nonnegative derivative $d$ on $[1-\varepsilon,1]$. If $F(1)-F(1-\varepsilon)\le B$, then $$\int_{1-\varepsilon}^{1} t\,d(t)\,dt\le B.$$ This is the integral inequality used after the influence identity in the proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Mathlib
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory

namespace StabilityDichotomies.Approximability
theorem weighted_influence_integral_bound
    (ε B : ℝ) (hε : 0 ≤ ε) (F d : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.uIcc (1 - ε) 1, HasDerivAt F (d t) t)
    (hint : IntervalIntegrable d volume (1 - ε) 1)
    (hnonneg : ∀ t ∈ Set.Icc (1 - ε) 1, 0 ≤ d t)
    (hbound : F 1 - F (1 - ε) ≤ B) :
    (∫ t in (1 - ε)..1, t * d t) ≤ B := by sorry
end StabilityDichotomies.Approximability
