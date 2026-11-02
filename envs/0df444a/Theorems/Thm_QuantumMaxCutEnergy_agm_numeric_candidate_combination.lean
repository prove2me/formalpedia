-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_numeric_candidate_combination
-- name    : QuantumMaxCutEnergy.agm_numeric_candidate_combination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:26:00.366181+00:00
-- url     : https://prove2.me/theorems/74b1a786-94e1-4a2e-b57d-1967e08a62e5
-- title:
--   AGM numerical candidate combination with no matching sampling loss
-- statement:
--   Let β≥0, and let W,m,f,O,E be real numbers. Suppose O≤W+(m+f)/2 and E dominates f, (W+3m)/2, and β(O+W)/3. Then 11βO≤(15+5β)E. In the QMC application, W is total edge weight, m and f are matching and forest weights, O is the optimum, and E is the expected maximum of the numerical candidates. No positivity of W or division by W is required, so zero-weight instances are covered. The theorem is a conditional algebraic combination, not a complete algorithm.
-- source:
--   Anshu, Gosset and Morenz, TQC2020, Lemma7 and Eqs24–27, pp7:9–7:10. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . Numerical-estimation adaptation: evaluate the exact matching mean from Eq25 directly rather than sample a matching state, retaining the coefficient1 instead of0.98.

import Mathlib.Data.Real.Basic

theorem QuantumMaxCutEnergy.agm_numeric_candidate_combination
    (β W m f O E : ℝ) (hβ : 0 ≤ β)
    (hupper : O ≤ W + (m + f) / 2) (hforest : f ≤ E)
    (hmatching : (W + 3 * m) / 2 ≤ E) (hproduct : β * (O + W) / 3 ≤ E) :
    11 * β * O ≤ (15 + 5 * β) * E := by sorry
