-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_theorem_6_sum_sq_regret
-- name    : StochLinOpt.ConfBall2.theorem_6_sum_sq_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:55:07.863142+00:00
-- url     : https://prove2.me/theorems/8bc3bba9-760a-4150-a480-0a9f21fb1de9
-- title:
--   Theorem 6 (ConfidenceBall$_2$, corrected: $T\ge2$): $\sum_{t=1}^T r_t^2\le 8n\beta_T\ln T$
-- statement:
--   Let $D\subset\mathbb R^n$ be compact and span $\mathbb R^n$, let $b$ be a barycentric spanner for $D$, let $0<\delta<1$, let $\mu$ satisfy $\mu^\top y\in[-1,1]$ for all $y\in D$, and let $x^*$ minimize $\mu^\top y$ over $D$. Let $(x_t,\ell_t)$ be a run of ConfidenceBall$_2(D,\delta)$ and $r_t=\mu^\top x_t-\mu^\top x^*$. For every $T\ge2$, if $\mu\in B^2_t$ for every $2\le t\le T$, then
--
--   $$\sum_{t=1}^T r_t^2\le 8\,n\,\beta_T\ln T .$$
--
--   The theorem is deterministic: on any run whose confidence ellipsoids keep containing $\mu$, the squared regrets are summable at a polylogarithmic rate. Combined with Theorem 5 and Cauchy–Schwarz it gives Theorem 2.
--
--   Differences from the source:
--   - correction: for every T (with μ ∈ B²_t for all t ≤ T) → for every T ≥ 2; reason: at T = 1 the bound 8nβ_1 ln 1 = 0 fails: n = 1, D = [−1/2, 1], b_1 = 1, μ = 1/2, δ = 1/2 give μ ∈ B²_1 (Z_1 = 1/4 ≤ β_1 ≈ 3.42), x_1 = 1, x* = −1/2 and r_1² = 9/16
--   - generalization: hypothesis μ ∈ B²_t for all t ≤ T → μ ∈ B²_t for 2 ≤ t ≤ T only; reason: a weaker hypothesis; it is what the corrected Theorem 5 (t ≥ 2) supplies
--   - reading: the parameter δ of ConfidenceBall2(D, δ), unconstrained in this statement → 0 < δ < 1; reason: the algorithm's parameter range stated in Theorem 2 ('Let 0 < δ < 1'); outside it the statement fails (δ = 4, T = 2, n = 1, D = [−1/2, 1], b_1 = 1, μ = 1/2, ℓ_1 = 1 give β_2 = 0, B²_2 = {µ̂_2} = {μ}, x_1 = 1 and Σ r_t² = 9/16 > 0)
--   - generalization: losses ℓ_t = c_t(x_t) ∈ [−1, 1] → any real sequence ℓ; reason: the proof uses only μ ∈ B²_t for 2 ≤ t ≤ T, the argmin rule, decisions in D and μ·y ∈ [−1, 1] on D (which gives r_t ≤ 2); the paper's losses are an instance
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
--   - encoding: B²_t = {ν : ‖ν − µ̂_t‖_{2,A_t} ≤ √β_t} → (ν − µ̂_t)ᵀ A_t (ν − µ̂_t) ≤ β_t; reason: equivalent because β_t ≥ 0
--   - encoding: x_t = argmin_{x∈D} min_{ν∈B²_t} νᵀx → x_t ∈ D and a joint minimizer (x_t, ν₀) of νᵀy over D × B²_t, with any tie-breaking; reason: equivalent since D and B²_t are compact and nonempty; the paper's argmin fixes no tie-breaking rule
--   - encoding: rounds t = 1, 2, … → sequences indexed by ℕ with only indices t ≥ 1 read; reason: same instances; index 0 is never used
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Theorem 6 (ConfidenceBall2 bullet), p. 7

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_IsConfBall2Run
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Theorem 6, ConfidenceBall₂ bullet (corrected: T ≥ 2)** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Theorem 6, p. 7: "Let
rt = µ · xt − µ · x∗ denote the instantaneous regret acquired by the algorithm on round t. For
ConfidenceBall2, if µ ∈ B2t for all t ≤ T, then Σ_{t=1}^T r2t ≤ 8nβT ln T").

Along any run of ConfidenceBall₂(D, δ) with `0 < δ < 1`, for every `T ≥ 2` such that `μ ∈ B²_t`
for every `2 ≤ t ≤ T`, `Σ_{t=1}^T r_t² ≤ 8n β_T ln T`.

**Formalization Note** At `T = 1` the printed bound is `0` and fails (`n = 1`, `D = [−1/2, 1]`,
`b_1 = 1`, `μ = 1/2`, `δ = 1/2` give `μ ∈ B²_1` and `r_1² = 9/16`), so `T ≥ 2`. The hypothesis
`μ ∈ B²_t` is required only for `2 ≤ t ≤ T`, which is weaker than the printed `t ≤ T`. -/
theorem theorem_6_sum_sq_regret {n : ℕ} {D : Set (Fin n → ℝ)} (hD : IsCompact D)
    (hfull : Submodule.span ℝ D = ⊤) {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {μ : Fin n → ℝ}
    (hμ : ∀ y ∈ D, μ ⬝ᵥ y ∈ Set.Icc (-1 : ℝ) 1) {xstar : Fin n → ℝ}
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y) {ℓ : ℕ → ℝ} {x : ℕ → Fin n → ℝ}
    (hrun : IsConfBall2Run D b δ ℓ x) (T : ℕ) (hT : 2 ≤ T)
    (hμT : ∀ t, 2 ≤ t → t ≤ T → μ ∈ confBall b x ℓ δ t) :
    ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 8 * n * beta n δ T * Real.log T := by sorry

end StochLinOpt.ConfBall2
