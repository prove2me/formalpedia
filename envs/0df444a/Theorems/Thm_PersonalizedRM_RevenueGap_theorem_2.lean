-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_theorem_2
-- name    : PersonalizedRM.RevenueGap.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:02.954756+00:00
-- url     : https://prove2.me/theorems/0879f55b-5aa5-46ea-9698-dcf3e0f01191
-- title:
--   Theorem 2, p. 17 — revenue convergence rate: high-probability revenue-gap bound for the decision optimal under the constrained MLE
-- statement:
--   For every $\psi > 0$ there is a constant $C_\psi > 0$ depending only on $\psi$, and for every $R > 0$ a constant $C(R,\psi) > 0$ depending only on $R$ and $\psi$, with the following property. Assume the personalized logit model with $J$ products, $d$ features and $n \ge 1$ historical transactions, satisfying Assumptions 1 and 2 (sub-Gaussian norm $\psi$, exploration level $\nu$, eigenvalue level $\rho$), with a true parameter $\|\theta^*\|_1 \le R$ and $\ell_1$-constrained maximum likelihood estimates $\hat\theta$ with radius $R$. Let $\mathcal S$ be any family of feasible assortments and $\mathcal P = [p_{\min}, 1]^J$ the price box. If $n \ge 4C_\psi\log(\nu n)/(\nu\min(\rho,1)^2)$, then with probability at least $1 - 1/n - 2J/(\nu n)$ the following holds for every feature vector $z$ with $\|z\|_\infty \le 1$: whenever $(S^*, p^*)$ maximizes $f_z(\cdot,\cdot;\theta^*)$ and $(\hat S, \hat p)$ maximizes $f_z(\cdot,\cdot;\hat\theta)$ over $\mathcal S \times \mathcal P$,
--
--   $$f_z(S^*, p^*; \theta^*) - f_z(\hat S, \hat p; \theta^*) \ \le\ \frac{C(R,\psi)}{\nu\rho}\, J^4(d+1) \sqrt{\frac{\log(2nJ(d+1))}{n}} .$$
--
--   The left-hand side is the revenue lost, under the true customer behaviour, by pricing and assorting with the estimated model instead of the true one. The theorem says that this loss is $\tilde O(1/\sqrt n)$, uniformly over customers, with explicit dependence on the number of products, the feature dimension and the richness of the historical data ($\nu$, $\rho$). It is an out-of-sample guarantee: it holds for any new customer.
--
--   **Formalization Note.** "With high probability" is pinned to probability at least $1 - 1/n - 2J/(\nu n)$, the event of Theorem 1, on which the proof (two applications of Proposition 1) works. The quantifier order is $\forall\psi\ \exists C_\psi\ \forall R\ \exists C(R,\psi)$, all before the data, so neither constant can depend on $J$, $d$, $n$, $\nu$, $\rho$, $p_{\min}$, $\mathcal S$ or the sample. The bound holds for every choice of maximizers, and uniformly in $z$ (the event does not depend on $z$). The hypothesis $n \ge 1$ is added because $1/n = 0$ in Lean at $n = 0$. The statement bounds the (outer) probability of the bad event, since the set of maximizers need not be measurable.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. 17, Theorem 2; proof p. 18

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Theorem 2 (Revenue Convergence Rate), p. 17: with probability at least
`1 − 1/n − 2J/(νn)`, as long as `n ≥ 4C_ψ log(νn)/(ν min(ρ,1)²)`, for every bounded feature
vector `z`, every decision `(S∗, p∗)` optimal under `θ∗` and every decision `(Ŝ, p̂)`
optimal under the constrained MLE `θ̂`,
`f_z(S∗, p∗; θ∗) − f_z(Ŝ, p̂; θ∗) ≤ C(R,ψ)/(νρ) · J⁴(d + 1) √(log(2nJ(d + 1))/n)`. -/
theorem theorem_2 : ∀ ψ : ℝ, 0 < ψ → ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n J d : ℕ) (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
      (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
      (θstar : Param J d) (θhat : Ω → Param J d) (pmin ν ρ : ℝ) (𝒮 : Set (Finset (Fin J))),
      0 < n →
      Assumption1 P S z price u y θstar pmin ψ → Assumption2 P S z price ν ρ →
      l1norm θstar ≤ R →
      (∀ ω, IsConstrainedMLE R
        (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω)) (θhat ω)) →
      4 * Cψ * Real.log (ν * n) / (ν * min ρ 1 ^ 2) ≤ n →
      P {ω | ¬ ∀ zz : Fin d → ℝ, (∀ k, |zz k| ≤ 1) →
          ∀ (Sstar : Finset (Fin J)) (pstar : Fin J → ℝ) (Shat : Finset (Fin J))
            (phat : Fin J → ℝ),
            IsOracleDecision 𝒮 pmin θstar zz Sstar pstar →
            IsOracleDecision 𝒮 pmin (θhat ω) zz Shat phat →
            revenue θstar zz Sstar pstar - revenue θstar zz Shat phat ≤
              C / (ν * ρ) * (J : ℝ) ^ 4 * ((d : ℝ) + 1) *
                Real.sqrt (Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) / n)}
        ≤ ENNReal.ofReal (1 / n + 2 * J / (ν * n)) := by sorry

end PersonalizedRM.RevenueGap
