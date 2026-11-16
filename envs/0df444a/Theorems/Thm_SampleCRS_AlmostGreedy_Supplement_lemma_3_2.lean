-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_lemma_3_2
-- name    : SampleCRS.AlmostGreedy.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:39:20.428088+00:00
-- url     : https://prove2.me/theorems/c7151d33-680a-4c08-84dd-8a375b7f4a70
-- title:
--   Lemma 3.2 — one-sample threshold error
-- statement:
--   Let $p\in[0,1]^n$ have total mass one, let $T$ be Algorithm 3's actual sample-based threshold, and put $\varepsilon_i=p_i/2-\Pr[T=i]$. Then for every element, including zero-bias elements,
--   $$\varepsilon_i\le\frac{1-1/e}{12}\,p_i(1-p_i).$$
--   The coefficient is the one stated in Lemma 3.2. This controls the threshold distribution error used in Theorem 3.4.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: threshold 0 before all arrivals and thresholds 1,…,n → none and some i : Option (Fin n); reason: a separate sentinel preserves strict-after-threshold eligibility at the first arrival
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Lemma 3.2, p. 13

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

namespace SampleCRS.AlmostGreedy.Supplement

/-- Lemma 3.2, p.13. one-sample threshold error. -/
theorem lemma_3_2 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1) :
    ∀ i : Fin n, thresholdError p i ≤ ((1 - 1 / Real.exp 1) / 12) * p i * (1 - p i) := by sorry

end SampleCRS.AlmostGreedy.Supplement
