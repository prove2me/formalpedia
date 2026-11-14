-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_harmonic_gap_ge_removed_fraction
-- name    : StabilityDichotomies.Bijunctive.harmonic_gap_ge_removed_fraction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:51:35.505335+00:00
-- url     : https://prove2.me/theorems/81d08d1a-0b21-4a8a-85a8-037e5a8618f4
-- title:
--   Harmonic gap dominates the fraction of removed candidates
-- statement:
--   For natural numbers $m\le n$, the harmonic-number difference satisfies $(n-m)/n\le H_n-H_m$, with the usual zero-denominator convention when $n=0$. This supports summing winner-change bounds over grouped removals.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root record analysis.

import Mathlib
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.harmonic_gap_ge_removed_fraction (m n : ℕ) (hmn : m ≤ n) :
    ((n - m : ℕ) : ℝ) / n ≤ (harmonic n : ℝ) - harmonic m := by
  sorry
