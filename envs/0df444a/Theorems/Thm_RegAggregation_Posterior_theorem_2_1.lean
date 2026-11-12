-- Prove2me | Theorems.Thm_RegAggregation_Posterior_theorem_2_1
-- name    : RegAggregation.Posterior.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:47.080433+00:00
-- url     : https://prove2.me/theorems/46b2a537-66c9-4631-bc1d-4cb52feedc8f
-- title:
--   Theorem 2.1, p. 10 — θ ∈ P(K): max{0, (Kγ² − γ)/(K − 1)} ≤ ρ < γ ≤ δ
-- statement:
--   Let $K\ge2$ and $\theta=(\delta,\gamma,\rho)\in\mathbb R^3$. Suppose the evidence covariance matrix $\Sigma$ (defined in the model) is positive definite, $\rho\ge0$ (Assumption 2.3, rational agreement) and $\delta-\gamma=\operatorname{Var}(N_k)\ge0$. Then
--   $$\theta \in \mathcal P(K) = \Big\{(\delta,\gamma,\rho) : \max\Big\{0,\tfrac{K\gamma^2-\gamma}{K-1}\Big\} \le \rho < \gamma \le \delta\Big\}.$$
--
--   This is the constraint set on which the whole Bayesian analysis takes place. In particular, the posterior of Theorem 3.3 is integrated over $\mathcal P(K)$.
--
--   **Formalization Note** The paper's sentence "the parameters in the likelihood (2) must satisfy" is formalized through the three facts its proof uses: $\Sigma \succ 0$, $\rho \ge 0$ and $\delta \ge \gamma$. These are the model's own assumptions (the proof, p. 36: "Given that ρ ≥ 0 (recall Assumption 2.3) and Var(N_k) = δ − γ ≥ 0"). The lower bound on $\rho$ is non-strict, as printed.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 10, Theorem 2.1 (proof pp. 35–36)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem theorem_2_1 (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ)
    (hSigma : (evidenceCov K θ).PosDef) (hρ : 0 ≤ θ 2) (hN : θ 1 ≤ θ 0) :
    θ ∈ PK K := by sorry

end RegAggregation.Posterior
