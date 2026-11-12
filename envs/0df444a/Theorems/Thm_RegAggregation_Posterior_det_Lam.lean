-- Prove2me | Theorems.Thm_RegAggregation_Posterior_det_Lam
-- name    : RegAggregation.Posterior.det_Lam
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:54.449196+00:00
-- url     : https://prove2.me/theorems/7ef2c764-4fea-4b9f-b0b1-cfba37a80494
-- title:
--   Proof of Theorem 3.2, p. 37 — det Λ22 = η1η2^{K−1}
-- statement:
--   Let $K\ge2$ and $\theta=(\delta,\gamma,\rho)\in\mathcal P(K)$. The covariance matrix of the probit predictions, $\Lambda_{22} = [(\delta-\rho)I_K + \rho J_K]/(1-\gamma)$, has determinant
--   $$\det \Lambda_{22} = \eta_1\, \eta_2^{K-1}, \qquad \eta_1 = \frac{\delta+(K-1)\rho}{1-\gamma},\quad \eta_2 = \frac{\delta-\rho}{1-\gamma}.$$
--
--   This is the normalizing factor of the Gaussian likelihood in Theorem 3.2.
--
--   **Formalization Note** The exponent $K-1$ is natural-number subtraction, which is harmless because $K\ge2$.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 37, proof of Theorem 3.2

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem det_Lam (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    (Lam K θ).det = eta1 K θ * eta2 θ ^ (K - 1) := by sorry

end RegAggregation.Posterior
