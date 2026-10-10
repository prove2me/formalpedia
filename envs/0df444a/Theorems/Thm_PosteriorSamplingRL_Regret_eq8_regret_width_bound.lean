-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_eq8_regret_width_bound
-- name    : PosteriorSamplingRL.Regret.eq8_regret_width_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:07:11.520487+00:00
-- url     : https://prove2.me/theorems/f06a544b-3829-4086-af16-71926b160136
-- title:
--   (8), §5.2, p. 7 — E[Σ Δ̃_k] ≤ (τ+1) E[Σ_k Σ_i min{β_k(s_{t_k+i}, a_{t_k+i}), 1}] + 2τ (factor corrected from τ)
-- statement:
--   Consider a PSRL run with $M^*\sim f$ and the confidence widths $\beta_k(s,a)$ built for $m$ episodes. Then
--   $$
--   \mathbb E\Big[\sum_{k=1}^m\tilde\Delta_k\Big]\le(\tau+1)\,\mathbb E\Big[\sum_{k=1}^m\sum_{i=1}^\tau\min\{\beta_k(s_{k,i},a_{k,i}),1\}\Big]+2\tau ,
--   $$
--   where $(s_{k,i},a_{k,i})$ is the state–action pair of step $i$ of episode $k$.
--
--   This bounds the expected regret by the total confidence width along the visited pairs, which the counting argument of Appendix B then sums.
--
--   **Formalization Note** The page prints the factor $\tau$ in front of the expectation. On the confidence event, $|\overline R^{M_k}-\overline R^{M^*}|\le2\beta$ and $\|P^{M_k}-P^{M^*}\|_1\le2\beta$, and $V^k_{\mu_k,i+1}$ takes values in $[0,\tau-i]$, so a Bellman error is at most $\min\{(\tau-i+2)\beta,\tau\}\le(\tau+1)\min\{\beta,1\}$. At $\tau=1$ the error can equal $2\beta$, which exceeds $\tau\min\{\beta,1\}=\beta$ for small $\beta$, so the page's last step (third line to fourth) does not follow from its argument. The printed final inequality is not known to be false, but the page does not establish it. The factor $\tau+1$ is what the page's own chain proves, and it is the factor stated here. For Theorem 1 the difference is absorbed into the absolute constant. The page's index $s_{t_k+i}$ is the $i$-th state of episode $k$ as in (6).
-- source:
--   arXiv:1306.0940v5, §5.2, (8), p. 7

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- (8), §5.2 (arXiv:1306.0940v5, p. 7), with the factor corrected from `τ` to `τ + 1`:
`E[∑_{k=1}^m Δ̃_k] ≤ (τ + 1) E[∑_{k=1}^m ∑_{i=1}^τ min{β_k(s_{t_k+i}, a_{t_k+i}), 1}] + 2τ`. -/
theorem eq8_regret_width_bound (S A τ : ℕ) (hS : 1 ≤ S) (hA : 1 ≤ A) (hτ : 1 ≤ τ)
    (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (hρ : IsDist ρ)
    (f : Measure Θ) (sel : Θ → Policy S A τ) (hsel : ∀ θ, IsOptimal F θ (sel θ))
    (hsel_meas : Measurable sel)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : PSRLRun F ρ f sel μ) (m : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range m, R.Δtilde k ω ∂μ
      ≤ ((τ : ℝ) + 1) * ∫ ω, ∑ k ∈ Finset.range m, ∑ j : Fin τ,
            min (R.β m k (R.st k j.castSucc ω) (R.act k j ω) ω) 1 ∂μ
        + 2 * τ := by sorry

end PosteriorSamplingRL.Regret
