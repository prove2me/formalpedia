-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P84_optical_cut_factor_two
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P84.optical_cut_factor_two
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:13:05.379919+00:00
-- url     : https://prove2.me/theorems/861dc3f4-0279-4a34-b513-f5c44e0ca394
-- title:
--   Optical cut weights differ by at most a factor of two
-- statement:
--   Fix a cut of a finite quantum network, and let $C$ denote its labelled crossing edges in both directions. For each $e\in C$, let $f_e\ge0$ be its frequency and let $0\le\eta_e<1$ be its intensity transmittance. Then
--
--   $$
--   \sum_{e\in C} f_e\log_2\!\left(\frac{1+\eta_e}{1-\eta_e}\right)
--   \le 2\sum_{e\in C} f_e\log_2\!\left(\frac{1}{1-\eta_e}\right).
--   $$
--
--   The inequality compares the two explicit optical cut weights uniformly over the cut, network topology, and frequencies. It remains valid for an empty cut or zero transmittances. Frequencies restricted to one cut need not sum to one.
--
--   **Formalization Note** The finite index type in Lean is precisely the set of crossing-edge labels. The inequality uses explicit real logarithms, rather than a ratio of capacities at zero transmittance.
-- source:
--   Aggregating quantum repeaters for the quantum internet, arXiv:1606.00135v1, PDF p. 4, Eq.(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P84

open QAlgorithms

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Eq.(13): the optical upper cut weight is at most twice the
achievable cut weight. `E` indexes just the crossing edges of the fixed cut;
parallel and oppositely directed links retain separate labels. No positivity
of the cut weight or normalization of its restricted frequencies is required. -/
theorem optical_cut_factor_two {E : Type*} [Fintype E]
    (frequency eta : E → ℝ)
    (hfrequency : ∀ e, 0 ≤ frequency e)
    (heta : ∀ e, 0 ≤ eta e ∧ eta e < 1) :
    (∑ e, frequency e * Real.logb 2 ((1 + eta e) / (1 - eta e))) ≤
      2 * ∑ e, frequency e * Real.logb 2 (1 / (1 - eta e)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P84

end
