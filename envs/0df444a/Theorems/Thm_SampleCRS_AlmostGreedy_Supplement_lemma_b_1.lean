-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_lemma_b_1
-- name    : SampleCRS.AlmostGreedy.Supplement.lemma_b_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:26.362614+00:00
-- url     : https://prove2.me/theorems/85266e2b-bef1-4e61-947b-eb8687d2a506
-- title:
--   Lemma B.1 — actual competing candidate-count comparison
-- statement:
--   Let $k\ge1$ and $p\in[0,1]^n$ have total mass $k$. With Appendix B's parameters $\beta_k=1-\gamma_k/\delta_k$, let the independent candidate bits have biases $\rho_j=p_j(1-\beta_kp_j)$ and let $G_i=\sum_{j\ne i}Z_j$. Then for every element, including those with $p_i=0$,
--   $$E[\operatorname{AR}_k(G_i)]\ge E[\operatorname{AR}_k(\operatorname{Poi}(k-p_i))].$$
--   The competitor distribution uses the candidate biases rather than the original activation probabilities. Its mean need not be $k-p_i$. This is the comparison used for Algorithm 6.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: G_i is a sum of independent candidate bits with biases ρ_j, j≠i → the published activation law at candidateBias followed by otherCount; reason: the omitted coordinate is counted nowhere; the unused independent coordinate averages out, giving exactly the same count law
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Lemma B.1, p. 41

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_scaling

namespace SampleCRS.AlmostGreedy.Supplement

/-- Lemma B.1, p.41. actual competing candidate-count comparison. -/
theorem lemma_b_1 {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ValidProb p) (hmass : (∑ i, p i) = (k : ℝ)) :
    ∀ i : Fin n, StaticProphetSec.poisE (StaticProphetSec.AR k)
      (Real.toNNReal ((k : ℝ) - p i)) ≤ competingAR k p i := by sorry

end SampleCRS.AlmostGreedy.Supplement
