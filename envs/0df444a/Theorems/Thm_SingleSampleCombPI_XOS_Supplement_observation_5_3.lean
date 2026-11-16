-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_observation_5_3
-- name    : SingleSampleCombPI.XOS.Supplement.observation_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:30.34294+00:00
-- url     : https://prove2.me/theorems/20206d79-eb21-40dd-a24f-29eedc906f1e
-- title:
--   Observation 5.3 — Quantile tails and capacity-truncated density mass
-- statement:
--   Let $r_i=(q_i,x_i)$ be valid nonnegative-density knapsack records, with total weight at least one, as assumed in §5.2. For every $t\ge0$, both the prophet-knapsack tail and its uniform random quantile satisfy
--   $$K_r(t)=\Pr[\tau_r>t\mid r]=\min\{1,\sum_i x_i\mathbf1[q_i>t]\}.$$
--   The conditional probability is represented by a uniform Lebesgue average on $[0,1]$.
--
--   Differences from the source:
--   - encoding: uniform density quantiles of a filled capacity-one optimum → a density sort and cumulative-weight scan with a null-endpoint fallback; reason: the scan has exactly the uniform quantile law; endpoint changes have measure zero and do not restrict weights or densities
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Observation 5.3, printed p. 28 / PDF p. 30; proof printed 28 / PDF 30.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Observation 5.3, PDF 30 / printed 28. Both equalities, under the
filled-profile standing assumption. The threshold t is nonnegative. -/
theorem observation_5_3 {n : ℕ} (r : Fin n → Item)
    (hr : ∀ i, ItemValid .divisible (r i)) (hf : 1 ≤ ∑ i, (r i).2)
    (t : ℝ) (ht : 0 ≤ t) :
    knapTail r t = uavg (fun u => if t < densityQuantile r u then 1 else 0) ∧
    knapTail r t = min 1 (∑ i, if t < (r i).1 then (r i).2 else 0) := by sorry

end SingleSampleCombPI.XOS.Supplement
