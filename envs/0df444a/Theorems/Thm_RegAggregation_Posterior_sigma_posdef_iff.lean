-- Prove2me | Theorems.Thm_RegAggregation_Posterior_sigma_posdef_iff
-- name    : RegAggregation.Posterior.sigma_posdef_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:51.702115+00:00
-- url     : https://prove2.me/theorems/6b85ac09-3afa-48f1-8c05-38450fc2c62f
-- title:
--   Proof of Theorem 2.1, p. 35 — Σ ≻ 0 iff (Kγ² − γ)/(K − 1) < ρ < γ
-- statement:
--   Let $K \ge 2$ and $\theta=(\delta,\gamma,\rho)\in\mathbb R^3$. Let
--   $$\Sigma = \begin{pmatrix} 1 & \gamma \mathbf 1_K' \\ \gamma \mathbf 1_K & (\gamma-\rho) I_K + \rho J_K \end{pmatrix}$$
--   be the covariance matrix of the evidence $(I_0, I_1,\dots,I_K)$, where $I_K$ is the identity and $J_K$ the all-ones matrix. Then $\Sigma$ is positive definite if and only if
--   $$\frac{K\gamma^2-\gamma}{K-1} < \rho < \gamma.$$
--
--   This is the characterization that the proof of Theorem 2.1 derives with the Schur complement. Together with $\rho \ge 0$ and $\delta \ge \gamma$, it yields the parameter space $\mathcal P(K)$.
--
--   **Formalization Note** Positive definiteness is Mathlib's `Matrix.PosDef`: the matrix is symmetric and $x^\top \Sigma x > 0$ for every $x \neq 0$. The rows and columns are indexed by `Option (Fin K)`, and `none` stands for $I_0$. The parameter $\delta$ does not enter $\Sigma$.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 35, proof of Theorem 2.1, displays (10), (11)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem sigma_posdef_iff (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) :
    (evidenceCov K θ).PosDef ↔
      ((K : ℝ) * θ 1 ^ 2 - θ 1) / ((K : ℝ) - 1) < θ 2 ∧ θ 2 < θ 1 := by sorry

end RegAggregation.Posterior
