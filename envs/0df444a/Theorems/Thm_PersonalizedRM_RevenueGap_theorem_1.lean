-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_theorem_1
-- name    : PersonalizedRM.RevenueGap.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:53.41937+00:00
-- url     : https://prove2.me/theorems/a98c398f-339a-4119-b66c-78a16577ecb1
-- title:
--   Theorem 1, p. 14 — parameter convergence rate of the ℓ1-constrained logit MLE
-- statement:
--   For every $\psi > 0$ there is a constant $C_\psi > 0$, depending only on $\psi$, with the following property. Let $R > 0$ and assume the personalized logit model with Assumptions 1 and 2 (sub-Gaussian norm $\psi$, exploration level $\nu$, eigenvalue level $\rho$), a true parameter with $\|\theta^*\|_1 \le R$, and $\ell_1$-constrained maximum likelihood estimates $\hat\theta$ with radius $R$. If $n \ge 1$ and $n \ge 4C_\psi\log(\nu n)/(\nu\min(\rho,1)^2)$, then with probability at least $1 - 1/n - 2J/(\nu n)$,
--
--   $$\|\hat\theta - \theta^*\|_2 \ \le\ 2\,\frac{[1 + e^{-R} + (J-1)e^R]^2}{e^{-R}\nu\rho}\, \sqrt{\frac{2J(d+1)\log(2nJ(d+1))}{n}} .$$
--
--   This is the finite-sample estimation guarantee of the paper: the constrained MLE converges to the true parameter at rate $\sqrt{\log n / n}$, with explicit dependence on $J$, $d$, $R$, $\nu$ and $\rho$. The revenue bounds of Proposition 1 and Theorem 2 are derived from it.
--
--   **Formalization Note.** The constant $C_\psi$ is quantified before $R$ and before all data, so it cannot depend on them. The statement bounds the (outer) probability of the event that the estimation error exceeds the bound, for every selection $\hat\theta$ of constrained minimizers. The hypothesis $n \ge 1$ is added because $1/n = 0$ in Lean at $n = 0$. The printed statement is kept exactly, including the factor $2$ and the threshold with $\log(\nu n)$: in the regime where the corrected Lemma 2 does not apply, the right-hand side exceeds $2R \ge \|\hat\theta - \theta^*\|_2$ once $C_\psi$ is large enough.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. 14, Theorem 1; proof p. 16

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Theorem 1 (Parameter Convergence Rate), p. 14: with probability at least
`1 − 1/n − 2J/(νn)`, the ℓ1-constrained MLE satisfies
`‖θ̂ − θ∗‖₂ ≤ 2[1 + exp(−R) + (J − 1) exp(R)]²/(exp(−R)νρ) · √(2J(d + 1) log(2nJ(d + 1))/n)`,
as long as `n ≥ 4C_ψ log(νn)/(ν min(ρ,1)²)` for a constant `C_ψ` depending only on `ψ`. -/
theorem theorem_1 : ∀ ψ : ℝ, 0 < ψ → ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ R : ℝ, 0 < R →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n J d : ℕ) (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
      (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
      (θstar : Param J d) (θhat : Ω → Param J d) (pmin ν ρ : ℝ),
      0 < n →
      Assumption1 P S z price u y θstar pmin ψ → Assumption2 P S z price ν ρ →
      l1norm θstar ≤ R →
      (∀ ω, IsConstrainedMLE R
        (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω)) (θhat ω)) →
      4 * Cψ * Real.log (ν * n) / (ν * min ρ 1 ^ 2) ≤ n →
      P {ω | ¬ ‖θhat ω - θstar‖ ≤
          2 * (1 + Real.exp (-R) + ((J : ℝ) - 1) * Real.exp R) ^ 2 / (Real.exp (-R) * ν * ρ) *
            Real.sqrt (2 * J * ((d : ℝ) + 1) * Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) / n)}
        ≤ ENNReal.ofReal (1 / n + 2 * J / (ν * n)) := by sorry

end PersonalizedRM.RevenueGap
