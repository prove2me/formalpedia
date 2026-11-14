-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_grouped_removal_fraction_sum_le_harmonic
-- name    : StabilityDichotomies.Bijunctive.grouped_removal_fraction_sum_le_harmonic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:52:29.14936+00:00
-- url     : https://prove2.me/theorems/1cd70b12-d1a5-4117-a080-ef325767bb19
-- title:
--   Grouped removal fractions sum to at most a harmonic number
-- statement:
--   If the nonnegative integers $m_0\ge m_1\ge\cdots\ge m_k$ count surviving candidates after successive grouped removals, then $\sum_{i<k}(m_i-m_{i+1})/m_i\le H_{m_0}$, using the zero-denominator convention.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root record analysis.

import Mathlib
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.grouped_removal_fraction_sum_le_harmonic (k : ℕ) (m : ℕ → ℕ)
    (hmono : ∀ i < k, m (i+1) ≤ m i) :
    (∑ i ∈ Finset.range k, ((m i - m (i+1) : ℕ) : ℝ) / m i) ≤ (harmonic (m 0) : ℝ) := by
  sorry
