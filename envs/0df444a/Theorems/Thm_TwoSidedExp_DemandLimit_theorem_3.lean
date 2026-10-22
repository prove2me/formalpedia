-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_theorem_3
-- name    : TwoSidedExp.DemandLimit.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:35.019092+00:00
-- url     : https://prove2.me/theorems/ce9ceb0d-65f1-4a5a-8be0-6a8cacbfd7d7
-- title:
--   Theorem 3, p. 20 — as λ/τ → 0 the naive CR estimator is unbiased and the naive LR estimator is generically biased
-- statement:
--   Consider the mean-field two-sided marketplace under the standing assumptions, and sequences $\lambda_n,\tau_n>0$ of arrival rates and holding scales with $\lambda_n/\tau_n\to0$ (a highly demand-constrained market), all other parameters fixed. Steady states of the TSR designs are taken along the sequence.
--
--   1. **CR is unbiased.** For every $0<a_C<1$, and for any steady states of the designs $(a_C,1)$, $(1,1)$ and $(0,0)$ along the sequence,
--   $$\frac{\widehat{\mathrm{GTE}}^{\mathrm{CR}}(\infty\mid a_C)}{\lambda_n}-\frac{\mathrm{GTE}}{\lambda_n}\longrightarrow0.$$
--   2. **LR is generically biased.** For every $0<a_L<1$ and for Lebesgue-almost every treatment-utility array $\tilde v=(\tilde v_\gamma(\theta))\in(0,\infty)^{\Gamma\times\Theta}$ (all other parameters fixed), there is a number $L\neq0$ such that along every sequence with $\lambda_n/\tau_n\to0$ and any steady states of the designs $(1,a_L)$, $(1,1)$, $(0,0)$ of the model with treatment utility $\tilde v$,
--   $$\frac{\widehat{\mathrm{GTE}}^{\mathrm{LR}}(\infty\mid a_L)}{\lambda_n}-\frac{\mathrm{GTE}}{\lambda_n}\longrightarrow L.$$
--
--   In a demand-constrained market, customer-side randomization estimates the global treatment effect without asymptotic bias, while listing-side randomization does not.
--
--   **Formalization Note** $Q_{ij}(\infty)$, and with it GTE and the estimators, is the right side of (18) at a steady state; steady states are quantified over rather than chosen, and the mission's §5.1 milestone shows they exist. The paper prints $\widehat{\mathrm{GTE}}^{\mathrm{LR}}(\infty\mid a_C)$ in the second sentence; the estimator indexed by $a_L$ is meant. Footnote 7 reads "generically" as "for all parameter values except a Lebesgue-null set"; read literally on the full parameter vector this is ill-posed, because $\rho$ and $\phi$ are constrained to simplices, which are themselves Lebesgue-null. The statement therefore fixes every other parameter and takes "almost every" in the treatment utility $\tilde v$ on the positive orthant; by Fubini it implies the footnote's reading on any product parameter set containing $\tilde v$ as a free coordinate. The paper's own argument for this half is informal ("in general, this limit will not be equivalent to the GTE"). The limit $L$ is required to be the same for every sequence, as "$\lim\ldots\neq0$" asserts.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 20, Theorem 3 and footnote 7

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Theorem 3, p. 20, with footnote 7. Along any sequence of systems with `λ/τ → 0`:
(CR) for every `0 < aC < 1`, `ĜTE^CR(∞|aC)/λ − GTE/λ → 0`;
(LR) for every `0 < aL < 1` and Lebesgue-almost every treatment-utility array `ṽ = w` in the
positive orthant, there is `L ≠ 0` with `ĜTE^LR(∞|aL)/λ − GTE/λ → L` along every such sequence. -/
theorem theorem_3 {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ) (hM : M.Standing) :
    (∀ aC : ℝ, 0 < aC → aC < 1 →
      ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
        Tendsto (fun n => lam n / tau n) atTop (𝓝 0) →
      ∀ (sCR sGT sGC : ℕ → Θ × Fin 2 → ℝ),
        (∀ n, (M.expt aC 1).IsSteady (lam n) (tau n) (sCR n)) →
        (∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
        (∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
      Tendsto (fun n => M.crEst (lam n) aC (sCR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 0)) ∧
    (∀ aL : ℝ, 0 < aL → aL < 1 →
      ∀ᵐ w ∂(volume : Measure (Γ → Θ → ℝ)), (∀ γ θ, 0 < w γ θ) →
        ∃ L : ℝ, L ≠ 0 ∧
          ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
            Tendsto (fun n => lam n / tau n) atTop (𝓝 0) →
          ∀ (sLR sGT sGC : ℕ → Θ × Fin 2 → ℝ),
            (∀ n, ((M.withVt w).expt 1 aL).IsSteady (lam n) (tau n) (sLR n)) →
            (∀ n, ((M.withVt w).expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
            (∀ n, ((M.withVt w).expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
          Tendsto (fun n => (M.withVt w).lrEst (lam n) aL (sLR n) / lam n
              - (M.withVt w).gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 L)) := by sorry

end TwoSidedExp.DemandLimit
