-- Prove2me | Theorems.Thm_RegAggregation_Posterior_fisher_det
-- name    : RegAggregation.Posterior.fisher_det
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:46.73678+00:00
-- url     : https://prove2.me/theorems/a86ca1e2-8067-4ba5-bdda-7dc2766f6548
-- title:
--   Proof of Theorem 3.3 (i), p. 39 — |I(θ)| = μ0²(K − 1)K³/(16(1 − γ)⁷η1³η2²)
-- statement:
--   Let $K\ge2$, $\mu_0\in\mathbb R$ and $\theta=(\delta,\gamma,\rho)\in\mathcal P(K)$. The Fisher information matrix $\mathcal I(\theta)$ of the likelihood of the probit predictions has determinant
--   $$|\mathcal I(\theta)| = \frac{\mu_0^2 (K-1) K^3}{16 (1-\gamma)^7 \eta_1^3 \eta_2^2}.$$
--   In particular, the Fisher information is singular exactly when $\mu_0 = 0$, that is, when $p_0 = 0.5$.
--
--   The determinant is the input of the Jeffreys prior $\pi_J(\theta) \propto |\mathcal I(\theta)|^{1/2}$.
--
--   **Formalization Note** The Fisher information is the expectation of products of score functions, computed with `deriv` and the Bochner integral (see the model). The paper orders $\theta$ as $(\delta,\rho,\gamma)$ in this proof; the determinant does not depend on the order.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 39, proof of Theorem 3.3 (i) (definition of the Fisher information p. 15, display (12) p. 37)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem fisher_det (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    (fisherInfo K μ0 θ).det =
      μ0 ^ 2 * ((K : ℝ) - 1) * (K : ℝ) ^ 3 /
        (16 * (1 - θ 1) ^ 7 * eta1 K θ ^ 3 * eta2 θ ^ 2) := by sorry

end RegAggregation.Posterior
