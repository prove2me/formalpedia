-- Prove2me | Theorems.Thm_RegAggregation_Posterior_theorem_3_3_i
-- name    : RegAggregation.Posterior.theorem_3_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:49.426635+00:00
-- url     : https://prove2.me/theorems/4750ef22-83c0-4415-b104-2502e1aa2711
-- title:
--   Theorem 3.3 (i), p. 17 — the Jeffreys prior exists iff p0 ≠ 0.5 and equals π(θ; 1, 1/2)
-- statement:
--   Let $K\ge2$ and $\mu_0\in\mathbb R$, with common prior $p_0=\Phi(\mu_0)$. Consider the prior family $\pi(\theta;a,b)\propto\eta_1^{-(a+1/2)}\eta_2^{-(b+1/2)}(1-\gamma)^{-(a+5/2)}$ on $\mathcal P(K)$. Then:
--
--   1. if $p_0 = 0.5$, the Fisher information determinant $|\mathcal I(\theta)|$ vanishes at every $\theta\in\mathcal P(K)$, so $|\mathcal I(\theta)|^{1/2}$ defines no prior;
--   2. if $p_0\ne 0.5$, there is a constant $C>0$ such that for every $\theta\in\mathcal P(K)$
--   $$\sqrt{|\mathcal I(\theta)|} = C\,\pi(\theta;1,1/2) = C\,\eta_1^{-3/2}\eta_2^{-1}(1-\gamma)^{-7/2}.$$
--
--   That is, the Jeffreys prior exists if and only if $p_0\neq0.5$, and it is then $\pi_J(\theta)=\pi(\theta;1,1/2)$.
--
--   **Formalization Note** "Exists" is read as "$|\mathcal I(\theta)|^{1/2}$ is not identically zero on $\mathcal P(K)$", and "equals" as "equal up to a positive constant", since the family is defined only up to proportionality. $p_0$ is `cdf (gaussianReal 0 1) μ0`.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 17, Theorem 3.3 (i) (proof p. 39)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem theorem_3_3_i (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) :
    (commonPrior μ0 = 1 / 2 → ∀ θ ∈ PK K, (fisherInfo K μ0 θ).det = 0) ∧
    (commonPrior μ0 ≠ 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ PK K,
        Real.sqrt (fisherInfo K μ0 θ).det = C * prior K 1 (1 / 2) θ) := by sorry

end RegAggregation.Posterior
