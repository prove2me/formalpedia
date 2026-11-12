-- Prove2me | Theorems.Thm_RegAggregation_Posterior_theorem_3_2
-- name    : RegAggregation.Posterior.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:47.618302+00:00
-- url     : https://prove2.me/theorems/5e776e89-b1d9-4047-a8ae-eee20439ce04
-- title:
--   Theorem 3.2, p. 15 — the likelihood (6) of the probit predictions in terms of P̄, S_P, η1, η2
-- statement:
--   Let $K\ge2$, $\mu_0\in\mathbb R$, $\theta=(\delta,\gamma,\rho)\in\mathcal P(K)$ and $\mathbf P\in\mathbb R^K$. Under the Gaussian model, $\eta_1=[\delta+(K-1)\rho]/(1-\gamma)$ and $\eta_2=(\delta-\rho)/(1-\gamma)$ are the eigenvalues of $\operatorname{Cov}(\mathbf P)=\Lambda_{22}=[(\delta-\rho)I_K+\rho J_K]/(1-\gamma)$, and it has no others. The likelihood of the probit predictions is
--   $$\pi(\mathbf P\mid p_0,\theta) = \frac{1}{\sqrt{(2\pi)^K\eta_1\eta_2^{K-1}}}\exp\left\{-\frac K2\left[\frac{S_P}{\eta_2} + \frac{\big(\bar P - \frac{\mu_0}{\sqrt{1-\gamma}}\big)^2}{\eta_1}\right]\right\},$$
--   with $\bar P = \frac1K\sum_k P_k$ and $S_P = \frac1K\sum_k P_k^2 - \bar P^2$.
--
--   Writing the $K$-variate likelihood in terms of the two sufficient statistics makes posterior computation cost constant in $K$ once $\bar P$ and $S_P$ are known.
--
--   **Formalization Note** "Unique eigenvalues" is stated as the spectrum of $\Lambda_{22}$ being the set $\{\eta_1,\eta_2\}$, which is a single point when $\rho = 0$. The left side is the Gaussian density written with determinant and matrix inverse (the model's `lik`), so the theorem is not a definitional unfolding.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 15, Theorem 3.2, display (6) (proof p. 37)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem theorem_3_2 (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K)
    (P : Fin K → ℝ) :
    spectrum ℝ (Lam K θ) = {eta1 K θ, eta2 θ} ∧
    lik K μ0 θ P =
      1 / Real.sqrt ((2 * Real.pi) ^ K * eta1 K θ * eta2 θ ^ (K - 1)) *
        Real.exp (-((K : ℝ) / 2) *
          (SP P / eta2 θ + (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / eta1 K θ)) := by sorry

end RegAggregation.Posterior
