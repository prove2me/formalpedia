-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_lemma_2
-- name    : PersonalizedRM.RevenueGap.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:03.769577+00:00
-- url     : https://prove2.me/theorems/ab00c2ed-972d-4bb0-b79b-17e7f3e8eb74
-- title:
--   Lemma 2, p. 16 (corrected) — ℓ_n is η-strongly convex on ‖θ‖₁ ≤ R with probability ≥ 1 − 2J/(νn)
-- statement:
--   Assume the personalized logit model with Assumptions 1 and 2 (sub-Gaussian norm $\psi$, exploration level $\nu$, eigenvalue level $\rho$), and let $R > 0$. There is a constant $C_\psi > 0$ depending only on $\psi$ with the following property. If $n \ge 1$,
--
--   $$n \ \ge\ \frac{4C_\psi \log(\nu n)}{\nu \min(\rho,1)^2} \qquad\text{and}\qquad \nu n \ \ge\ \frac{4 C_\psi J(d+1)}{\min(\rho,1)^2},$$
--
--   then, with probability at least $1 - 2J/(\nu n)$, the negative log-likelihood $\ell_n$ is strongly convex on the ball $\{\theta : \|\theta\|_1 \le R\}$ with parameter
--
--   $$\eta = \frac{e^{-R}\nu\rho}{2[1 + e^{-R} + (J-1)e^R]^2}. \tag{6}$$
--
--   Strong convexity with parameter $\eta$ means $\ell_n(t\theta + (1-t)\theta') \le t\ell_n(\theta) + (1-t)\ell_n(\theta') - \frac{\eta}{2} t(1-t)\|\theta - \theta'\|_2^2$ for feasible $\theta, \theta'$ and $t \in [0,1]$, equivalently $v^\top \nabla^2 \ell_n(\theta) v \ge \eta \|v\|_2^2$ for feasible $\theta$ (EC.4). Together with the gradient bound of Lemma 1 it yields the parameter rate of Theorem 1.
--
--   **Formalization Note.** The second threshold, $\nu n \ge 4C_\psi J(d+1)/\min(\rho,1)^2$, is added: it corrects the printed statement, which is false without it. With $J = 1$, Rademacher features and $d + 1 > n$, the empirical second-moment matrix has rank at most $n < d+1$, so $\ell_n$ is never strongly convex, while every large $n$ meets the printed threshold. The proof on p. ec4 applies Vershynin's Corollary 5.50 with $t = \sqrt{\log(\nu n)/(J(d+1))}$, which requires $t \ge 1$; the added condition is what the argument needs when it is run with $\max(t, 1)$, with the same probability. The statement is an upper bound on the (outer) probability of the event that $\ell_n$ is not $\eta$-strongly convex. The proof uses neither the outcomes nor $\|\theta^*\|_1 \le R$, which is not assumed here. Strong convexity is Mathlib's `StrongConvexOn`, whose modulus convention matches (4).
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. 16, Lemma 2, (6); proof pp. ec2–ec5, (EC.4)–(EC.9)

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Lemma 2 (Strong Convexity), p. 16, corrected: with probability at least `1 − 2J/(νn)` the
negative log-likelihood is strongly convex on the ℓ1 ball `‖θ‖₁ ≤ R` with parameter
`η = exp(−R)νρ / (2[1 + exp(−R) + (J − 1) exp(R)]²)` of (6). Besides the printed threshold
`n ≥ 4C_ψ log(νn)/(ν min(ρ,1)²)` it assumes `νn ≥ 4C_ψ J(d + 1)/min(ρ,1)²`, without which the
printed statement fails when `d + 1 > n`. -/
theorem lemma_2 : ∀ ψ : ℝ, 0 < ψ → ∃ Cψ : ℝ, 0 < Cψ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n J d : ℕ) (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
      (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
      (θstar : Param J d) (pmin ν ρ R : ℝ),
      0 < n → 0 < R →
      Assumption1 P S z price u y θstar pmin ψ → Assumption2 P S z price ν ρ →
      4 * Cψ * Real.log (ν * n) / (ν * min ρ 1 ^ 2) ≤ n →
      4 * Cψ * ((J : ℝ) * ((d : ℝ) + 1)) / min ρ 1 ^ 2 ≤ ν * n →
      P {ω | ¬ StrongConvexOn {θ : Param J d | l1norm θ ≤ R} (etaSC J R ν ρ)
          (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω))}
        ≤ ENNReal.ofReal (2 * J / (ν * n)) := by sorry

end PersonalizedRM.RevenueGap
