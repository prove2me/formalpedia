-- Prove2me | Theorems.Thm_RegAggregation_Posterior_KS1_ge_S2
-- name    : RegAggregation.Posterior.KS1_ge_S2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:48.667872+00:00
-- url     : https://prove2.me/theorems/5b2fe773-6392-46f9-8ba7-eea204a6961e
-- title:
--   Proof of Theorem 3.3, p. 40 — KS1 ≥ S2, strictly when the P_k are not all equal
-- statement:
--   Let $K\in\mathbb N$, $\mu_0\in\mathbb R$ and $\mathbf P\in\mathbb R^K$. Let
--   $$S_1 = \sum_{k=1}^K (P_k-\mu_0)^2,\qquad S_2 = \sum_{i,k}(P_k-\mu_0)(P_i-\mu_0).$$
--   Then $K S_1 \ge S_2$. If, moreover, $P_i\neq P_k$ for some $i\neq k$, then $K S_1 > S_2$.
--
--   In the proof of Theorem 3.3 (iii), this is what makes the scale of the inverse gamma integral in $\lambda_2$ strictly positive when the forecasters disagree.
--
--   **Formalization Note** The page writes the upper limit of the sum in $S_1$ as $N$; it is the number $K$ of forecasters.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 40, proof of Theorem 3.3 (iii)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem KS1_ge_S2 (K : ℕ) (μ0 : ℝ) (P : Fin K → ℝ) :
    S2 μ0 P ≤ (K : ℝ) * S1 μ0 P ∧
    ((∃ i k, i ≠ k ∧ P i ≠ P k) → S2 μ0 P < (K : ℝ) * S1 μ0 P) := by sorry

end RegAggregation.Posterior
