-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_lemma_14_martingale_bound
-- name    : StochLinOpt.ConfBall2.lemma_14_martingale_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:57:54.609979+00:00
-- url     : https://prove2.me/theorems/c7e0aae2-4d30-4bdc-aa69-04c6dc9145bf
-- title:
--   Lemma 14: $P(\forall t,\ \sum_{\tau<t}M_\tau\le\beta_t/2)\ge1-\delta$
-- statement:
--   Assume the stochastic linear model on $(\Omega,P)$ with a compact decision set $D$ spanning $\mathbb R^n$ and barycentric spanner $b$, let $0<\delta<1$, and let the decisions be a run of ConfidenceBall$_2(D,\delta)$ on every outcome. Then
--
--   $$P\Bigl(\forall t\ge1:\ \sum_{\tau=1}^{t-1}M_\tau\le\frac{\beta_t}{2}\Bigr)\ge1-\delta .$$
--
--   The event is uniform in $t$. It is the high-probability event on which the induction of Theorem 5 runs.
--
--   Differences from the source:
--   - reading: Given δ < 1 → 0 < δ < 1; reason: δ is the parameter of ConfidenceBall2(D, δ), whose range is 0 < δ < 1 (Theorem 2); β_t is undefined for δ ≤ 0
--   - encoding: ∀t → ∀ t ≥ 1; reason: rounds are 1-based; at t = 1 the sum is empty
--   - generalization: E(c_t(x) | H_t) = μ·x for all x ∈ D, ℓ_t = c_t(x_t) ∈ [−1, 1] → losses ℓ_t ∈ [−1, 1], x_t H_t-measurable, E(ℓ_t | H_t) = μ·x_t a.s. (IsStochLinEnv); reason: the paper's assumption implies the loss-level one because x_t is determined by H_t (proof of Lemma 13, p. 9); the analysis uses only the latter
--   - encoding: x_t = argmin_{x∈D} min_{ν∈B²_t} νᵀx → x_t ∈ D and a joint minimizer (x_t, ν₀) of νᵀy over D × B²_t, with any tie-breaking; reason: equivalent since D and B²_t are compact and nonempty; the paper's argmin fixes no tie-breaking rule
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
--   - encoding: B²_t = {ν : ‖ν − µ̂_t‖_{2,A_t} ≤ √β_t} → (ν − µ̂_t)ᵀ A_t (ν − µ̂_t) ≤ β_t; reason: equivalent because β_t ≥ 0
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 14, p. 9

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_IsStochLinEnv
import Definitions.Def_StochLinOpt_ConfBall2_IsConfBall2Run
import Definitions.Def_StochLinOpt_ConfBall2_martM
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Lemma 14** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 14, p. 9: "Given δ < 1, Prob(∀t, Σ_{τ=1}^{t−1} Mτ ≤ βt/2) ≥ 1 − δ").

In the stochastic linear model, along ConfidenceBall₂(D, δ) with `0 < δ < 1`, with probability at
least `1 − δ`, `Σ_{τ=1}^{t−1} M_τ ≤ β_t/2` holds for every round `t ≥ 1` simultaneously.

**Formalization Note** The event is uniform in `t` (the quantifier is inside the probability).
`0 < δ` is the algorithm's parameter range (Theorem 2: "Let 0 < δ < 1"). No bound on the noise
beyond `ℓ_t ∈ [−1, 1]` is assumed. -/
theorem lemma_14_martingale_bound {n : ℕ} {D : Set (Fin n → ℝ)} (hD : IsCompact D)
    (hfull : Submodule.span ℝ D = ⊤) {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {μ : Fin n → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℓ : ℕ → Ω → ℝ) (x : ℕ → Ω → Fin n → ℝ) (henv : IsStochLinEnv P μ D ℓ x)
    (hrun : ∀ ω, IsConfBall2Run D b δ (fun t => ℓ t ω) (fun t => x t ω)) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | ∀ t : ℕ, 1 ≤ t →
        ∑ τ ∈ Finset.Ico 1 t, martM b (fun s => x s ω) (fun s => ℓ s ω) μ δ τ ≤ beta n δ t / 2} := by sorry

end StochLinOpt.ConfBall2
