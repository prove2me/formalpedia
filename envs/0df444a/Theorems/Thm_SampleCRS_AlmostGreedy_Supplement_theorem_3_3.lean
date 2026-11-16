-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_3_3
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:13.650572+00:00
-- url     : https://prove2.me/theorems/c8e23fb0-9a58-4de6-a55f-4b75d1c77603
-- title:
--   Theorem 3.3 — exact two-sample threshold distribution
-- statement:
--   Let $p\in[0,1]^n$ have total mass one. Draw the two independent sample rows and carry out Algorithm 2's actual threshold choices. Its threshold $T$ has exactly the law
--   $$\Pr[T=0]=1/2,\qquad\Pr[T=i]=p_i/2\quad\text{for every }i\in[n].$$
--   The second equality includes $p_i=0$ and $p_i=1$. This describes the algorithm's output law, rather than merely the existence of an ideal threshold or a balancedness consequence.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: threshold 0 before all arrivals and thresholds 1,…,n → none and some i : Option (Fin n); reason: a separate sentinel preserves strict-after-threshold eligibility at the first arrival
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 3.3, p. 10

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem 3.3, p.10. exact two-sample threshold distribution. -/
theorem theorem_3_3 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1) :
    threshold2Law p none = (1 / 2 : ℝ) ∧
    ∀ i : Fin n, threshold2Law p (some i) = p i / 2 := by sorry

end SampleCRS.AlmostGreedy.Supplement
