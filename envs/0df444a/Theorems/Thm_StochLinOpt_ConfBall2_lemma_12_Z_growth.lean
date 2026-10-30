-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_lemma_12_Z_growth
-- name    : StochLinOpt.ConfBall2.lemma_12_Z_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:55:53.614008+00:00
-- url     : https://prove2.me/theorems/bd58616e-dba2-4978-bfc3-be97a5ac7304
-- title:
--   Lemma 12: growth bound for $Z_t$
-- statement:
--   Let $D\subset\mathbb R^n$ span $\mathbb R^n$, let $b$ be a barycentric spanner for $D$ and let $\mu$ satisfy $\mu^\top y\in[-1,1]$ for all $y\in D$. For any decisions $x_\tau$ and losses $\ell_\tau$, with $\eta_\tau=\ell_\tau-\mu^\top x_\tau$, for every round $t\ge1$,
--
--   $$Z_t\le n+2\sum_{\tau=1}^{t-1}\eta_\tau\,\frac{x_\tau^\top(\widehat\mu_\tau-\mu)}{1+w_\tau^2}+\sum_{\tau=1}^{t-1}\eta_\tau^2\,\frac{w_\tau^2}{1+w_\tau^2}.$$
--
--   The lemma splits the estimation error into a martingale part, controlled in Lemma 14, and a predictable part, controlled by Lemma 9.
--
--   Differences from the source:
--   - generalization: the algorithm's decisions and losses → arbitrary sequences x, ℓ; reason: the proof is algebra on A_{t+1} = A_t + x_t x_tᵀ (Sherman–Morrison); the run is an instance
--   - generalization: spanner normalized to the standard basis, Z_1 = ‖μ‖² ≤ n → any barycentric spanner; Z_1 = μᵀA_1μ = Σ_i (μ·b_i)² ≤ n; reason: with b_i = e_i this is the paper's Z_1
--   - encoding: for all t → for all t ≥ 1; reason: rounds are 1-based
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 12, p. 9

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_errZ
import Definitions.Def_StochLinOpt_ConfBall2_noise
import Definitions.Def_StochLinOpt_ConfBall2_width
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Lemma 12** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 12, p. 9: "For all t,
Zt ≤ n + 2 Σ_{τ=1}^{t−1} ητ x†τ(µ̂τ − µ)/(1 + w2τ) + Σ_{τ=1}^{t−1} η2τ w2τ/(1 + w2τ)").

For every round `t ≥ 1`,
`Z_t ≤ n + 2 Σ_{τ=1}^{t−1} η_τ x_τᵀ(µ̂_τ − μ)/(1 + w_τ²) + Σ_{τ=1}^{t−1} η_τ² w_τ²/(1 + w_τ²)`,
where `η_τ = ℓ_τ − μ ⬝ x_τ`.

**Formalization Note** `μ ⬝ y ∈ [−1, 1]` on `D` (the standing model; with `b_i ∈ D` it gives
`Z_1 = Σ_i (μ ⬝ b_i)² ≤ n`). The decisions and losses are arbitrary sequences: the lemma is an
algebraic consequence of the update `A_{t+1} = A_t + x_t x_tᵀ`. -/
theorem lemma_12_Z_growth {n : ℕ} {D : Set (Fin n → ℝ)} (hfull : Submodule.span ℝ D = ⊤)
    {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b) {μ : Fin n → ℝ}
    (hμ : ∀ y ∈ D, μ ⬝ᵥ y ∈ Set.Icc (-1 : ℝ) 1) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ)
    (ht : 1 ≤ t) :
    errZ b x ℓ μ t ≤ n
      + 2 * (∑ τ ∈ Finset.Ico 1 t,
          noise μ x ℓ τ * (x τ ⬝ᵥ (lsEst b x ℓ τ - μ)) / (1 + width b x τ ^ 2))
      + (∑ τ ∈ Finset.Ico 1 t,
          noise μ x ℓ τ ^ 2 * width b x τ ^ 2 / (1 + width b x τ ^ 2)) := by sorry

end StochLinOpt.ConfBall2
