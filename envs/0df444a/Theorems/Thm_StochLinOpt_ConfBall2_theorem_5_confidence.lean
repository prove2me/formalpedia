-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_theorem_5_confidence
-- name    : StochLinOpt.ConfBall2.theorem_5_confidence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:58:39.630186+00:00
-- url     : https://prove2.me/theorems/05532978-c1d9-4aba-b239-22dcddd60492
-- title:
--   Theorem 5 (ConfidenceBall$_2$, corrected: $t\ge2$): $P(\forall t\ge2,\ \mu\in B^2_t)\ge1-\delta$
-- statement:
--   Assume the stochastic linear model on $(\Omega,P)$ with a compact decision set $D$ spanning $\mathbb R^n$ and barycentric spanner $b$, let $\delta>0$, and let the decisions be a run of ConfidenceBall$_2(D,\delta)$ on every outcome. Then
--
--   $$P\bigl(\forall t\ge2:\ \mu\in B^2_t\bigr)\ge1-\delta .$$
--
--   The confidence ellipsoids contain the true mean at all rounds from the second on, simultaneously, with probability at least $1-\delta$. This is the probabilistic half of the proof of Theorem 2.
--
--   Differences from the source:
--   - correction: ∀t (including t = 1) → ∀ t ≥ 2, for every δ > 0; reason: μ ∈ B²_1 is the deterministic condition μᵀA_1μ ≤ β_1, which fails for large δ: n = 1, D = [−1/2, 1], b_1 = 1, μ = 1, ℓ_t = x_t, δ = 0.9 give Z_1 = 1 > β_1 ≈ 0.079, so the probability is 0 < 0.1
--   - generalization: E(c_t(x) | H_t) = μ·x for all x ∈ D, ℓ_t = c_t(x_t) ∈ [−1, 1] → losses ℓ_t ∈ [−1, 1], x_t H_t-measurable, E(ℓ_t | H_t) = μ·x_t a.s. (IsStochLinEnv); reason: the paper's assumption implies the loss-level one because x_t is determined by H_t (proof of Lemma 13, p. 9); the analysis uses only the latter
--   - encoding: x_t = argmin_{x∈D} min_{ν∈B²_t} νᵀx → x_t ∈ D and a joint minimizer (x_t, ν₀) of νᵀy over D × B²_t, with any tie-breaking; reason: equivalent since D and B²_t are compact and nonempty; the paper's argmin fixes no tie-breaking rule
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
--   - encoding: B²_t = {ν : ‖ν − µ̂_t‖_{2,A_t} ≤ √β_t} → (ν − µ̂_t)ᵀ A_t (ν − µ̂_t) ≤ β_t; reason: equivalent because β_t ≥ 0
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Theorem 5 (ConfidenceBall2 bullet), p. 6

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_IsStochLinEnv
import Definitions.Def_StochLinOpt_ConfBall2_IsConfBall2Run
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Theorem 5, ConfidenceBall₂ bullet (corrected: t ≥ 2)** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Theorem 5, p. 6: "(Confidence)
Let δ > 0. For ConfidenceBall2, Prob (∀t, µ ∈ B2t) ≥ 1 − δ").

In the stochastic linear model, along any run of ConfidenceBall₂(D, δ) with `δ > 0`, with
probability at least `1 − δ`, `μ ∈ B²_t` for every round `t ≥ 2` simultaneously.

**Formalization Note** At `t = 1`, `μ ∈ B²_1` is the deterministic condition `μᵀA_1μ ≤ β_1`, which
fails for large `δ` (`n = 1`, `D = [−1/2, 1]`, `b_1 = 1`, `μ = 1`, `ℓ_t = x_t`, `δ = 0.9`:
`Z_1 = 1 > β_1 ≈ 0.079`), so the statement starts at `t = 2`, for every `δ > 0`. -/
theorem theorem_5_confidence {n : ℕ} {D : Set (Fin n → ℝ)} (hD : IsCompact D)
    (hfull : Submodule.span ℝ D = ⊤) {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b)
    {δ : ℝ} (hδ0 : 0 < δ) {μ : Fin n → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℓ : ℕ → Ω → ℝ) (x : ℕ → Ω → Fin n → ℝ) (henv : IsStochLinEnv P μ D ℓ x)
    (hrun : ∀ ω, IsConfBall2Run D b δ (fun t => ℓ t ω) (fun t => x t ω)) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | ∀ t : ℕ, 2 ≤ t → μ ∈ confBall b (fun s => x s ω) (fun s => ℓ s ω) δ t} := by sorry

end StochLinOpt.ConfBall2
