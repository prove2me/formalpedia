-- Prove2me | Theorems.Thm_RegAggregation_Posterior_theorem_3_3_iii
-- name    : RegAggregation.Posterior.theorem_3_3_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:50.940603+00:00
-- url     : https://prove2.me/theorems/e1ab63b0-557d-4539-aee6-57c2e8c2dff6
-- title:
--   Theorem 3.3 (iii), p. 17 — if some P_j ≠ P_k and P̄ ≠ μ0, the posterior under π(θ; a, b), a, b > 0, is proper
-- statement:
--   Let $K\ge2$ forecasters report probit predictions $\mathbf P=(P_1,\dots,P_K)\in\mathbb R^K$, and let the common prior be $p_0=\Phi(\mu_0)$ with $\mu_0\in\mathbb R$. Let $a>0$ and $b>0$, and consider the prior
--   $$\pi(\theta;a,b)\propto \eta_1^{-(a+1/2)}\,\eta_2^{-(b+1/2)}\,(1-\gamma)^{-(a+5/2)}$$
--   on the parameter space $\mathcal P(K)$, where $\eta_1=[\delta+(K-1)\rho]/(1-\gamma)$ and $\eta_2=(\delta-\rho)/(1-\gamma)$. Suppose
--   1. $P_j\neq P_k$ for some $j\neq k$, and
--   2. $\bar P = \frac1K\sum_{k=1}^K P_k \neq \mu_0$.
--
--   Then the posterior $\pi(\theta\mid p_0,\mathbf P)\propto\pi(\mathbf P\mid p_0,\theta)\,\pi(\theta;a,b)$ is proper:
--   $$0 < \int_{\mathcal P(K)} \pi(\mathbf P\mid p_0,\theta)\,\pi(\theta;a,b)\,d\theta < \infty.$$
--   Here $\pi(\mathbf P\mid p_0,\theta)$ is the density of the $K$-variate Gaussian distribution with mean $\mathbf 1_K\mu_0/\sqrt{1-\gamma}$ and covariance $[(\delta-\rho)I_K+\rho J_K]/(1-\gamma)$.
--
--   The family contains the Jeffreys prior $(a,b)=(1,1/2)$ and the independence Jeffreys prior $(a,b)=(1/2,1/2)$. The theorem guarantees that Bayesian aggregation of the forecasts with these objective priors is well defined as soon as the forecasters disagree and their mean probit differs from the prior's.
--
--   **Formalization Note** "Proper" is formalized as: the Lebesgue integral over $\mathcal P(K)\subset\mathbb R^3$ of likelihood times prior, taken in $[0,\infty]$, is strictly positive and finite. Then likelihood times prior, divided by this integral, is a probability density on $\mathcal P(K)$. The data $\mathbf P$ and $\mu_0$ are the probit images $\Phi^{-1}(p_k)$ and $\Phi^{-1}(p_0)$, a bijection $(0,1)\to\mathbb R$. The likelihood is the Gaussian density with determinant and inverse, not its closed form (6). The theorem is stated for every $a,b>0$, as on the page.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 17, Theorem 3.3 (iii) (proof pp. 39–41)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem theorem_3_3_iii (K : ℕ) (hK : 2 ≤ K) (μ0 a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (P : Fin K → ℝ) (hP : ∃ j k, j ≠ k ∧ P j ≠ P k) (hPbar : Pbar P ≠ μ0) :
    0 < ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) ∧
    ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) < ⊤ := by sorry

end RegAggregation.Posterior
