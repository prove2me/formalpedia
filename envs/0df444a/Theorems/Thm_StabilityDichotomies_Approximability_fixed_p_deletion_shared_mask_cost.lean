-- Prove2me | Theorems.Thm_StabilityDichotomies_Approximability_fixed_p_deletion_shared_mask_cost
-- name    : StabilityDichotomies.Approximability.fixed_p_deletion_shared_mask_cost
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:08:41.441214+00:00
-- url     : https://prove2.me/theorems/36ea4c03-4686-424f-b06d-ea10626fe84b
-- title:
--   Exact shared-mask deletion coupling cost at fixed retention probability
-- statement:
--   Fix a finite set of coordinates, any assignment-valued map of Boolean masks, and an arbitrary real p. Sum Hamming cost with independent Bernoulli-p mask weights for the shared-mask coupling between the original output and the output with coordinate i forced absent. The resulting weighted cost is exactly p times the weighted forced-present versus forced-absent Hamming distance. In the probability range 0 ≤ p ≤ 1 this is the fixed-p coupling-cost identity used in the source sensitivity argument. Identifying the forced-absent law with the separately enumerated deleted instance and integrating the coupling remain separate obligations.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem StabilityDichotomies.Approximability.fixed_p_deletion_shared_mask_cost {ι V : Type} [Fintype ι] [Fintype V]
    (out : (ι → Bool) → V → Bool) (p : ℝ) (i : ι) :
    (∑ x : ι → Bool, (∏ j : ι, if x j then p else 1-p) *
      (hammingDist (out x) (out (Function.update x i false)) : ℝ)) =
    p * ∑ x : ι → Bool, (∏ j : ι, if x j then p else 1-p) *
      (hammingDist (out (Function.update x i true)) (out (Function.update x i false)) : ℝ) := by sorry
