-- Prove2me | Theorems.Thm_RiskBalancingMNL_eq_2_3
-- name    : RiskBalancingMNL.eq_2_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:43:25.97238+00:00
-- url     : https://prove2.me/theorems/3a6cbc01-095e-49da-9fa6-5bdc202d5419
-- title:
--   Eqs (2)–(3) — mean and variance of the profit $\hat\pi=\sum_im_iX_i$
-- statement:
--   Let $N$ customers choose independently, each choosing product $i$ with probability $q_i$ and nothing otherwise, let $X_i$ be the demand for product $i$, and let $\hat\pi=\sum_im_iX_i$ be the profit at markups $m\in\mathbb R^n$. Then
--   $$
--   \mathbb E(\hat\pi)=N\sum_{i=1}^n m_iq_i \qquad (2)
--   $$
--   and
--   $$
--   \operatorname{Var}(\hat\pi)=m^{\mathsf T}\Sigma(X)m=N\Big(\sum_i m_i^2q_i(1-q_i)-\sum_i\sum_{j\ne i}m_im_jq_iq_j\Big)=N\Big(\sum_im_i^2q_i-\Big(\sum_im_iq_i\Big)^2\Big),\qquad (3)
--   $$
--   where $\Sigma(X)$ is the covariance matrix of $X$.
--
--   These identities show that the mean-variance utility of profit is $N$ times $\pi-\hat\lambda(g-\pi^2)$, which is how the objective $L=\pi^2-\lambda g$ of the mission arises.
--
--   Differences from the source:
--   - encoding: the multinomial demand vector of N customers → N independent choices with a common law ν on the products and the no-purchase option, X_i the number of customers choosing i; reason: this is the model of §3, p.7; the demand vector it produces is the multinomial vector of (1)
--   - encoding: Σ(X) given by the matrix (1) → the matrix of covariances Cov(X_i, X_j); reason: Σ(X) is the covariance matrix of X, whose entries (1) displays
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), eqs (2)–(3), p.8

import Mathlib
import Definitions.Def_RiskBalancingMNL_randomProfit

open MeasureTheory ProbabilityTheory

namespace RiskBalancingMNL

/-- **Eqs (2) and (3)**, Li & Webster, *Optimizing Risk-balancing Return under Discrete Choice
Models*, SSRN 3959428 (PDF of 2021-11-14), p.8. Let `N` customers choose independently, each with
law `ν` on `Fin n ⊕ Unit` (product `i` with probability `qᵢ`, nothing otherwise), let `Xᵢ` be the
demand for product `i` and `π̂ = Σᵢ mᵢ Xᵢ` the profit for markups `m`. Then
`E(π̂) = N Σᵢ mᵢ qᵢ` (2), and
`Var(π̂) = mᵀ Σ(X) m = N(Σᵢ mᵢ² qᵢ(1 − qᵢ) − Σᵢ Σ_{j≠i} mᵢ mⱼ qᵢ qⱼ) = N(Σᵢ mᵢ² qᵢ − (Σᵢ mᵢ qᵢ)²)` (3),
where `Σ(X)` is the covariance matrix of `X`.

**Formalization Note** The choice law `ν` is arbitrary: §3 has not fixed the choice model yet,
and (2)–(3) use only that the demand vector is multinomial. `Σ(X)` is written through
`covariance (Xᵢ) (Xⱼ)`. -/
theorem eq_2_3 {n : ℕ} (N : ℕ) (ν : Measure (Fin n ⊕ Unit)) [IsProbabilityMeasure ν]
    (m : Fin n → ℝ) :
    (∫ ω, randomProfit m ω ∂(customerLaw N ν)) = (N : ℝ) * ∑ i, m i * choiceProb ν i ∧
    variance (randomProfit (N := N) m) (customerLaw N ν) =
      ∑ i, ∑ j, m i * m j * covariance (demand (N := N) i) (demand j) (customerLaw N ν) ∧
    variance (randomProfit (N := N) m) (customerLaw N ν) =
      (N : ℝ) * (∑ i, m i ^ 2 * choiceProb ν i * (1 - choiceProb ν i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, m i * m j * choiceProb ν i * choiceProb ν j) ∧
    variance (randomProfit (N := N) m) (customerLaw N ν) =
      (N : ℝ) * (∑ i, m i ^ 2 * choiceProb ν i - (∑ i, m i * choiceProb ν i) ^ 2) := by sorry

end RiskBalancingMNL
