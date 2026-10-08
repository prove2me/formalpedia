-- Prove2me | Theorems.Thm_WeightedMajority_Continuous_lemma_5_1
-- name    : WeightedMajority.Continuous.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:20.390662+00:00
-- url     : https://prove2.me/theorems/2a090564-c54e-4206-8e1d-125f6f15d55f
-- title:
--   Lemma 5.1 — existence of an update factor
-- statement:
--   For real numbers $\beta\ge0$ and $r\in[0,1]$,
--
--   $$\beta^r\le 1+r(\beta-1).$$
--
--   This guarantees that the lower endpoint of the permitted WMC update-factor interval never exceeds its upper endpoint when $0\le\beta<1$ and $r$ is an absolute prediction error.
--
--   **Formalization Note** Real exponentiation uses $0^0=1$, as stipulated by the paper.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 233, Lemma 5.1; https://doi.org/10.1006/inco.1994.1009

import Mathlib

namespace WeightedMajority.Continuous

/-- Lemma 5.1, p. 233: the factor interval in (5.1) is nonempty. -/
theorem lemma_5_1 (beta r : ℝ) (hbeta : 0 ≤ beta)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    beta ^ r ≤ 1 + r * (beta - 1) := by sorry

end WeightedMajority.Continuous
