-- Prove2me | Theorems.Thm_RegAggregation_Posterior_quadratic_form
-- name    : RegAggregation.Posterior.quadratic_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:01.817997+00:00
-- url     : https://prove2.me/theorems/304ff2a0-854a-45e6-b1e6-9172342d550e
-- title:
--   Proof of Theorem 3.2, p. 37 — the Gaussian quadratic form equals K[S_P/η2 + (P̄ − μ0/√(1−γ))²/η1]
-- statement:
--   Let $K\ge2$, $\mu_0\in\mathbb R$, $\theta=(\delta,\gamma,\rho)\in\mathcal P(K)$ and $\mathbf P\in\mathbb R^K$. Write $m = \mathbf 1_K\,\mu_0/\sqrt{1-\gamma}$. Then
--   $$(\mathbf P - m)'\,\Lambda_{22}^{-1}\,(\mathbf P - m) = K\left[\frac{S_P}{\eta_2} + \frac{\big(\bar P - \mu_0/\sqrt{1-\gamma}\big)^2}{\eta_1}\right],$$
--   where $\bar P = \frac1K\sum_k P_k$ and $S_P = \frac1K\sum_k P_k^2 - \bar P^2$.
--
--   This identity reduces the $K$-dimensional Gaussian exponent to the two sufficient statistics $\bar P$ and $S_P$.
--
--   **Formalization Note** $\Lambda_{22}^{-1}$ is Mathlib's matrix inverse. On $\mathcal P(K)$ the matrix $\Lambda_{22}$ is invertible, so it is the true inverse.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 37, proof of Theorem 3.2

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model
open Matrix

namespace RegAggregation.Posterior

theorem quadratic_form (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K)
    (P : Fin K → ℝ) :
    (fun k => P k - μ0 / Real.sqrt (1 - θ 1)) ⬝ᵥ
        ((Lam K θ)⁻¹ *ᵥ (fun k => P k - μ0 / Real.sqrt (1 - θ 1))) =
      (K : ℝ) * (SP P / eta2 θ + (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / eta1 K θ) := by sorry

end RegAggregation.Posterior
