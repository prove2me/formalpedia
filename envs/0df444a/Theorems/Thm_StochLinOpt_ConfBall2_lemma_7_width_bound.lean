-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_lemma_7_width_bound
-- name    : StochLinOpt.ConfBall2.lemma_7_width_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:53:34.216874+00:00
-- url     : https://prove2.me/theorems/d4bfb98c-7482-4b65-8e7d-9444ab70e077
-- title:
--   Lemma 7 (ConfidenceBall$_2$): $|(\nu-\widehat\mu_t)^\top x|\le\sqrt{\beta_t\,x^\top A_t^{-1}x}$ on the confidence ellipsoid
-- statement:
--   Let $D\subset\mathbb R^n$ span $\mathbb R^n$ and let $b$ be a barycentric spanner for $D$. Let $x_1,x_2,\dots$ be any decisions, $\ell_1,\ell_2,\dots$ any losses and $\delta$ any real number. Then for every round $t\ge1$, every $\nu\in B^2_t$ and every $x\in D$,
--
--   $$\bigl|(\nu-\widehat\mu_t)^\top x\bigr|\le\sqrt{\beta_t\,x^\top A_t^{-1}x}.$$
--
--   This is Cauchy–Schwarz in the $A_t$-geometry; it converts membership in the confidence ellipsoid into a bound on prediction error in a given direction.
--
--   Differences from the source:
--   - generalization: decisions and losses of ConfidenceBall2(D, δ) → arbitrary sequences x, ℓ and any real δ; reason: the proof uses only ν ∈ B²_t and A_t ≻ 0; the algorithm's run is an instance and β_t ≥ 0 for every δ
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
--   - encoding: B²_t = {ν : ‖ν − µ̂_t‖_{2,A_t} ≤ √β_t} → (ν − µ̂_t)ᵀ A_t (ν − µ̂_t) ≤ β_t; reason: equivalent because β_t ≥ 0
--   - encoding: rounds t = 1, 2, … → sequences indexed by ℕ with only indices t ≥ 1 read; reason: same instances; index 0 is never used
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 7 (ConfidenceBall2 bullet), p. 7

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_confBall
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Lemma 7, ConfidenceBall₂ bullet** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 7, p. 7: "For ConfidenceBall2, if ν ∈ B2t and
x ∈ D. Then |(ν − µ̂t)†x| ≤ √(βt x†A−1t x)").

For every round `t ≥ 1`, every `ν ∈ B²_t` and every `y ∈ D`,
`|(ν − µ̂_t)ᵀ y| ≤ √(β_t yᵀ A_t⁻¹ y)`.

**Formalization Note** `D` spans `ℝⁿ` and `b` is a barycentric spanner of `D`, so `A_t` is
positive definite and `A_t⁻¹` is the true inverse. The decisions `x` and losses `ℓ` are arbitrary
(the lemma does not use how they were chosen); `δ` is arbitrary since `β_t ≥ 0` for every `δ`. -/
theorem lemma_7_width_bound {n : ℕ} {D : Set (Fin n → ℝ)} (hfull : Submodule.span ℝ D = ⊤)
    {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (δ : ℝ) (t : ℕ) (ht : 1 ≤ t) {ν : Fin n → ℝ} (hν : ν ∈ confBall b x ℓ δ t)
    {y : Fin n → ℝ} (hy : y ∈ D) :
    |(ν - lsEst b x ℓ t) ⬝ᵥ y| ≤ Real.sqrt (beta n δ t * (y ⬝ᵥ ((gram b x t)⁻¹ *ᵥ y))) := by sorry

end StochLinOpt.ConfBall2
