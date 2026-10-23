-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_proposition_1
-- name    : PersonalizedRM.RevenueGap.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:53.878966+00:00
-- url     : https://prove2.me/theorems/0099dd59-878f-403a-8202-f48100c04ede
-- title:
--   Proposition 1, p. 17 — uniform revenue forecast error ≤ C(R,ψ)/(2νρ)·J⁴(d + 1)√(log(2nJ(d + 1))/n) w.h.p.
-- statement:
--   For every $\psi > 0$ there is a constant $C_\psi > 0$ depending only on $\psi$, and for every $R > 0$ a constant $C(R,\psi) > 0$ depending only on $R$ and $\psi$, with the following property. Assume the personalized logit model with Assumptions 1 and 2, a true parameter with $\|\theta^*\|_1 \le R$, and $\ell_1$-constrained maximum likelihood estimates $\hat\theta$ with radius $R$. If $n \ge 1$ and $n \ge 4C_\psi \log(n)/(\nu\min(\rho,1)^2)$, then with probability at least $1 - 1/n - 2J/(\nu n)$, simultaneously for every assortment $S \subseteq [J]$, every price vector $p \in \mathcal P$ and every feature vector $z$ with $\|z\|_\infty \le 1$,
--
--   $$|f_z(S, p; \theta^*) - f_z(S, p; \hat\theta)| \ \le\ \frac{C(R,\psi)}{2\nu\rho}\, J^4(d+1) \sqrt{\frac{\log(2nJ(d+1))}{n}} .$$
--
--   The estimated model therefore forecasts the expected revenue of every decision, for every customer, to within $\tilde O(1/\sqrt n)$. Applied twice, this gives the revenue-gap bound of Theorem 2.
--
--   **Formalization Note.** "With high probability" is pinned to probability at least $1 - 1/n - 2J/(\nu n)$, the event of Theorem 1, which the proof uses. The page fixes $S$ and $p$ before the probability statement; here they are inside the event, which is stronger and is what the proof gives. The constants are quantified before all data. The threshold has $\log(n)$, as printed. The statement bounds the (outer) probability of the bad event.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. 17, Proposition 1; proof pp. 17–18

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Proposition 1, p. 17: with probability at least `1 − 1/n − 2J/(νn)`, as long as
`n ≥ 4C_ψ log(n)/(ν min(ρ,1)²)`, the revenue forecast error is at most
`C(R,ψ)/(2νρ) · J⁴(d + 1) √(log(2nJ(d + 1))/n)` simultaneously for every assortment, every price
vector in `P` and every bounded feature vector. -/
theorem proposition_1 : ∀ ψ : ℝ, 0 < ψ → ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n J d : ℕ) (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
      (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
      (θstar : Param J d) (θhat : Ω → Param J d) (pmin ν ρ : ℝ),
      0 < n →
      Assumption1 P S z price u y θstar pmin ψ → Assumption2 P S z price ν ρ →
      l1norm θstar ≤ R →
      (∀ ω, IsConstrainedMLE R
        (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω)) (θhat ω)) →
      4 * Cψ * Real.log n / (ν * min ρ 1 ^ 2) ≤ n →
      P {ω | ¬ ∀ Sa : Finset (Fin J), ∀ p ∈ priceBox J pmin, ∀ zz : Fin d → ℝ,
          (∀ k, |zz k| ≤ 1) →
          |revenue θstar zz Sa p - revenue (θhat ω) zz Sa p| ≤
            C / (2 * ν * ρ) * (J : ℝ) ^ 4 * ((d : ℝ) + 1) *
              Real.sqrt (Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) / n)}
        ≤ ENNReal.ofReal (1 / n + 2 * J / (ν * n)) := by sorry

end PersonalizedRM.RevenueGap
