-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_lemma_3_1
-- name    : SampleCRS.AlmostGreedy.Supplement.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:47.209281+00:00
-- url     : https://prove2.me/theorems/aa7d7aa7-89c4-440f-881f-72fd42972b41
-- title:
--   Lemma 3.1 — ideal threshold balancedness
-- statement:
--   Fix independent online activations with biases $p\in[0,1]^n$ of total mass one, and independently choose $T$ with $\Pr[T=0]=1/2$ and $\Pr[T=i]=p_i/2$. The scheme that accepts the first online-active arrival strictly after $T$ is feasible and
--   $$C_i\ge1/2\quad(p_i>0).$$
--   This ideal-threshold baseline is used in the analysis of Algorithm 3. Independence is represented by multiplying the threshold law by the entire online product law.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: threshold 0 before all arrivals and thresholds 1,…,n → none and some i : Option (Fin n); reason: a separate sentinel preserves strict-after-threshold eligibility at the first arrival
--   - encoding: a threshold random variable independent of X → its finite marginal law w, multiplied by the online law; reason: independence makes the joint law exactly this product; the stated atom masses already imply nonnegativity and normalization
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Lemma 3.1, p. 10

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

namespace SampleCRS.AlmostGreedy.Supplement

/-- Lemma 3.1, p.10. ideal threshold balancedness. -/
theorem lemma_3_1 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1)
    (w : Threshold n → ℝ) (hzero : w none = (1 / 2 : ℝ))
    (hatoms : ∀ i : Fin n, w (some i) = p i / 2) :
    ThresholdFeasible n ∧ ∀ i, 0 < p i → (1 / 2 : ℝ) ≤ thresholdC p w i := by sorry

end SampleCRS.AlmostGreedy.Supplement
