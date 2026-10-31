-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_iid_empirical_entropy_concentration
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.iid_empirical_entropy_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:07:19.973834+00:00
-- url     : https://prove2.me/theorems/7c9ee167-1c74-4780-9042-589653d05099
-- title:
--   Theorem 5: two-sided empirical-entropy concentration
-- statement:
--   Let p be a probability law on an alphabet of size 2^d and let n>=2 independent samples have the product law. Let Hhat be their plug-in entropy in bits, M its actual expectation under this same law, and r=sqrt(2 (log_2 n)^2 ln(2/epsilon)/n). For 0<epsilon<1, Pr[|Hhat-M|>=r]<=epsilon. The source cites Antos and Kontoyiannis. The n=1 endpoint is corrected as recorded below.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 18, Theorem 5, D28

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.18, Theorem 5 (D28), Antos--Kontoyiannis: two-sided concentration
around the actual iid expectation of empirical entropy. Printed: no n>=2 guard.
Changed: n>=2, since at n=1 the radius is zero and the inclusive event is certain.
No accepted concentration theorem is needed to state this result with sorry. -/
theorem iid_empirical_entropy_concentration
    (d n : ℕ) (hn : 2 ≤ n) (p : Fin (2 ^ d) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon < 1) :
    let mean := ∑ word : Fin n → Fin (2 ^ d),
      (∏ i, p (word i)) * empiricalEntropy word
    iidWordProbability p n (fun word =>
      |empiricalEntropy word - mean| ≥
        Real.sqrt (2 * (Real.logb 2 n) ^ 2 * Real.log (2 / epsilon) / n)) ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
