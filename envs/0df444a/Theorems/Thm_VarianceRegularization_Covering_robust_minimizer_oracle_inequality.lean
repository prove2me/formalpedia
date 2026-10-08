-- Prove2me | Theorems.Thm_VarianceRegularization_Covering_robust_minimizer_oracle_inequality
-- name    : VarianceRegularization.Covering.robust_minimizer_oracle_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:33.701178+00:00
-- url     : https://prove2.me/theorems/f47e6770-2fd4-446c-9135-797fe3400bef
-- title:
--   Theorem 3, (16) — oracle inequality for the χ²-robust minimizer
-- statement:
--   Let $\mathcal F$ be a nonempty class of measurable functions $f : \mathcal X \to [M_0, M_1]$, $M = M_1 - M_0$, and let $X_1, \dots, X_n$ ($n \ge 1$) be i.i.d. with law $P$, with empirical distribution $\widehat P_n$. Write $\mathbb E[f] = \int f\,dP$ and $\mathrm{Var}(f)$ for the variance of $f(X)$. Let $N_\infty(\mathcal F, \epsilon, 2n)$ be the empirical $\ell_\infty$ covering number, and call $\widehat f \in \mathcal F$ a **robust minimizer** if
--   $$
--   \widehat f \in \operatorname*{argmin}_{f \in \mathcal F} \left\{ \sup_P \left\{ \mathbb E_P[f(X)] : D_\phi(P\|\widehat P_n) \le \frac{\rho}{n} \right\} \right\},
--   $$
--   where $D_\phi$ is the divergence with $\phi(t) = \frac12 (t-1)^2$. If $n \ge 8M^2/t$, $t \ge \log 12$, $\epsilon > 0$ and $\rho \ge 9t$, then with probability at least $1 - 2(3N_\infty(\mathcal F, \epsilon, 2n) + 1)e^{-t}$, every robust minimizer satisfies
--   $$
--   \mathbb E[\widehat f(X)] \le \inf_{f \in \mathcal F} \left\{ \mathbb E[f] + 2\sqrt{\frac{2\rho}{n}\mathrm{Var}(f)} \right\} + \frac{19 M\rho}{3n} + \left(2 + 4\sqrt{\frac{2t}{n}}\right)\epsilon .
--   $$
--
--   The robust minimizer thus competes with the best variance-penalized population risk in the class, with an $O(1/n)$ remainder, instead of the $O(1/\sqrt n)$ remainder of empirical risk minimization when low-risk functions have small variance.
--
--   **Formalization Note** The sample is the coordinate process of $P^{\otimes n}$; the robust risk is the maximum over weight vectors in the $\chi^2$ ball. The statement covers every minimizer at once: the bad event is "some $g \in \mathcal F$ minimizing the robust risk at the sample violates the inequality", and its (outer) probability is bounded by $2(3N_\infty + 1)e^{-t}$ in $[0, \infty]$; if no minimizer exists the event is empty. The infimum is over the nonempty class $\mathcal F$ and every term is at least $M_0$, so the real infimum is the true one.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 11, Theorem 3, inequality (16)

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup
import Definitions.Def_VarianceRegularization_Covering_empCoveringNumber

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Covering

/-- Theorem 3, inequality (16) (Duchi–Namkoong, arXiv:1610.02581v3, p. 11): let `F` be a
nonempty class of measurable functions `X → [M₀, M₁]`, `M = M₁ - M₀`, `X₁,…,Xₙ` i.i.d. with
law `P`, `n ≥ 8M²/t`, `t ≥ log 12`, `ε > 0`, `ρ ≥ 9t`. With probability at least
`1 - 2(3 N∞(F, ε, 2n) + 1) e^{-t}`, every minimizer `f̂` over `F` of the robust risk
`sup_{P : D_φ(P‖P̂ₙ) ≤ ρ/n} E_P[f(X)]` satisfies
`E[f̂(X)] ≤ inf_{f ∈ F} {E[f] + 2√(2ρ Var(f)/n)} + 19Mρ/(3n) + (2 + 4√(2t/n)) ε`.
Stated as: the event where some robust minimizer `g` violates (16) has (outer) measure at most
`2(3 N∞(F, ε, 2n) + 1) e^{-t}` in `ℝ≥0∞`. The infimum is over the subtype `F`, which is
nonempty, and every term is at least `M₀`, so the real `⨅` is the true infimum. -/
theorem robust_minimizer_oracle_inequality {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (F : Set (X → ℝ)) (hFne : F.Nonempty) (M0 M1 : ℝ) (hM : M0 ≤ M1)
    (hF : ∀ f ∈ F, Measurable f ∧ ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t ρ ε : ℝ)
    (hnt : 8 * (M1 - M0) ^ 2 / t ≤ n) (ht : Real.log 12 ≤ t) (hε : 0 < ε) (hρ : 9 * t ≤ ρ) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∃ g ∈ F, (∀ f ∈ F, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
          (⨅ f : F, (∫ x, (f : X → ℝ) x ∂P
              + 2 * Real.sqrt (2 * ρ / n * variance (f : X → ℝ) P)))
            + 19 * (M1 - M0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
            < ∫ x, g x ∂P}
      ≤ 2 * (3 * (empCoveringNumber F ε (2 * n) : ENNReal) + 1)
          * ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Covering
