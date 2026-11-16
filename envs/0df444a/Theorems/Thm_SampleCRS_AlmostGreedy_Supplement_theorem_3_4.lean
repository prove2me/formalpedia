-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_3_4
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:22.997685+00:00
-- url     : https://prove2.me/theorems/c1c3e5e0-8313-425d-83f9-862ce4851c0a
-- title:
--   Theorem 3.4 — strict 0.48 balance of Algorithm 3
-- statement:
--   For every unknown $p\in[0,1]^n$ with total mass one, Algorithm 3 chooses its threshold from one independent sample row and then accepts the first active arrival strictly after it. Every realization produces an active subset of size at most one. For every $i$ with $p_i>0$,
--   $$C_i>0.48=12/25.$$
--   The inequality is strict. Arrival-position labels encode any fixed adversarial order, and the probability averages the actual sample and threshold choices.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: threshold 0 before all arrivals and thresholds 1,…,n → none and some i : Option (Fin n); reason: a separate sentinel preserves strict-after-threshold eligibility at the first arrival
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 3.4, p. 12

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem 3.4, p.12. strict 0.48 balance of Algorithm 3. -/
theorem theorem_3_4 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1) :
    ThresholdFeasible n ∧ ∀ i, 0 < p i → (12 / 25 : ℝ) < thresholdC p (threshold3Law p) i := by sorry

end SampleCRS.AlmostGreedy.Supplement
