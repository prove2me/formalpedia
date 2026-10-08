-- Prove2me | Theorems.Thm_VarianceRegularization_Covering_robust_risk_certificate
-- name    : VarianceRegularization.Covering.robust_risk_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:24.553932+00:00
-- url     : https://prove2.me/theorems/28d2c5a7-d430-4163-9e9c-d30904e673e2
-- title:
--   Theorem 3, (15) — the robust risk upper-bounds the population risk uniformly over F
-- statement:
--   Let $\mathcal F$ be a class of measurable functions $f : \mathcal X \to [M_0, M_1]$, $M = M_1 - M_0$, and let $X_1, \dots, X_n$ ($n \ge 1$) be i.i.d. with law $P$, with empirical distribution $\widehat P_n$. For $\rho \ge 0$ the robust risk of $f$ is $\sup_{P : D_\phi(P\|\widehat P_n) \le \rho/n} \mathbb E_P[f(X)]$, where $D_\phi$ is the $\chi^2$-type divergence with $\phi(t) = \frac12(t-1)^2$. Let $N_\infty(\mathcal F, \epsilon, 2n)$ be the empirical $\ell_\infty$ covering number. If $n \ge 8M^2/t$, $t \ge \log 12$, $\epsilon > 0$ and $\rho \ge 9t$, then with probability at least $1 - 2(3N_\infty(\mathcal F, \epsilon, 2n) + 1)e^{-t}$,
--   $$
--   \mathbb E[f(X)] \le \sup_{P : D_\phi(P\|\widehat P_n) \le \frac{\rho}{n}} \mathbb E_P[f(X)] + \frac{11}{3}\frac{M\rho}{n} + \left(2 + 4\sqrt{\frac{2t}{n}}\right)\epsilon \qquad \text{for all } f \in \mathcal F.
--   $$
--
--   The robust risk is therefore, up to an $O(1/n)$ term, a uniform upper confidence bound on the population risk: it certifies the quality of every element of $\mathcal F$, in particular of the robust minimizer.
--
--   **Formalization Note** The sample is the coordinate process of $P^{\otimes n}$, and the robust risk is the maximum of $\sum_i p_i f(X_i)$ over weight vectors $p$ in the $\chi^2$ ball. The statement bounds the (outer) probability of the event where some $f \in \mathcal F$ violates the inequality by $2(3N_\infty + 1)e^{-t}$, computed in $[0, \infty]$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 11, Theorem 3, inequality (15)

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup
import Definitions.Def_VarianceRegularization_Covering_empCoveringNumber

open MeasureTheory

namespace VarianceRegularization.Covering

/-- Theorem 3, inequality (15) (Duchi–Namkoong, arXiv:1610.02581v3, p. 11): let `F` be a class
of measurable functions `X → [M₀, M₁]`, `M = M₁ - M₀`, `X₁,…,Xₙ` i.i.d. with law `P`,
`n ≥ 8M²/t`, `t ≥ log 12`, `ε > 0`, `ρ ≥ 9t`. With probability at least
`1 - 2(3 N∞(F, ε, 2n) + 1) e^{-t}`, for all `f ∈ F`,
`E[f(X)] ≤ sup_{P : D_φ(P‖P̂ₙ) ≤ ρ/n} E_P[f(X)] + (11/3) Mρ/n + (2 + 4√(2t/n)) ε`.
Stated as: the event where some `f ∈ F` violates (15) has (outer) measure at most
`2(3 N∞(F, ε, 2n) + 1) e^{-t}` in `ℝ≥0∞`. -/
theorem robust_risk_certificate {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (F : Set (X → ℝ)) (M0 M1 : ℝ) (hM : M0 ≤ M1)
    (hF : ∀ f ∈ F, Measurable f ∧ ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t ρ ε : ℝ)
    (hnt : 8 * (M1 - M0) ^ 2 / t ≤ n) (ht : Real.log 12 ≤ t) (hε : 0 < ε) (hρ : 9 * t ≤ ρ) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∃ f ∈ F, robustRisk ρ f s + 11 / 3 * ((M1 - M0) * ρ / n)
          + (2 + 4 * Real.sqrt (2 * t / n)) * ε < ∫ x, f x ∂P}
      ≤ 2 * (3 * (empCoveringNumber F ε (2 * n) : ENNReal) + 1)
          * ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Covering
