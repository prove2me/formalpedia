-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_theorem_2_confidence_ball2_regret
-- name    : StochLinOpt.ConfBall2.theorem_2_confidence_ball2_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:59:17.451238+00:00
-- url     : https://prove2.me/theorems/edd63016-7158-4e7c-9d19-ea96f594ab6a
-- title:
--   Theorem 2 (ConfidenceBall$_2$): high-probability regret bound $R_T\le\sqrt{8nT\beta_T\ln T}$ for all $T$ (corrected: $T\ge2$)
-- statement:
--   Let $D\subset\mathbb R^n$ be a compact decision set that spans $\mathbb R^n$, let $b$ be a barycentric spanner for $D$, let $0<\delta<1$, and let $x^*$ minimize $\mu^\top y$ over $D$. Assume the stochastic linear model: losses $\ell_t\in[-1,1]$ with $\mathbb E(\ell_t\mid\mathcal H_t)=\mu^\top x_t$, $\mu^\top y\in[-1,1]$ on $D$, and decisions determined by the history $\mathcal H_t=\sigma(\ell_1,\dots,\ell_{t-1})$. If the decisions are a run of ConfidenceBall$_2(D,\delta)$ on every outcome, then, with
--
--   $$\beta_T=\max\Bigl(128\,n\ln T\ln(T^2/\delta),\ \bigl(\tfrac83\ln(T^2/\delta)\bigr)^2\Bigr),$$
--
--   $$P\Bigl(\forall T\ge2:\ R_T\le\sqrt{8\,n\,T\,\beta_T\ln T}\Bigr)\ge1-\delta .$$
--
--   So with high probability the regret of ConfidenceBall$_2$ is $O^*(n\sqrt T)$ at every horizon at once, with no dependence on the size of $D$; Theorem 3 of the paper shows the dependence on $n$ and $T$ cannot be improved.
--
--   Differences from the source:
--   - correction: Prob(∀T, R_T ≤ √(8nTβ_T ln T)) → Prob(∀T ≥ 2, R_T ≤ √(8nTβ_T ln T)); reason: at T = 1 the bound is 0: n = 1, D = [−1/2, 1], b_1 = 1, ℓ_t = x_t/2 (μ = 1/2), any δ give x_1 = 1, x* = −1/2 and R_1 = 3/4 on every outcome, so the probability is 0 < 1 − δ; the paper's prose says 'for all sufficiently large T'
--   - generalization: E(c_t(x) | H_t) = μ·x for all x ∈ D, ℓ_t = c_t(x_t) ∈ [−1, 1] → losses ℓ_t ∈ [−1, 1], x_t H_t-measurable, E(ℓ_t | H_t) = μ·x_t a.s. (IsStochLinEnv); reason: the paper's assumption implies the loss-level one because x_t is determined by H_t (proof of Lemma 13, p. 9); the analysis uses only the latter
--   - encoding: x_t = argmin_{x∈D} min_{ν∈B²_t} νᵀx → x_t ∈ D and a joint minimizer (x_t, ν₀) of νᵀy over D × B²_t, with any tie-breaking; reason: equivalent since D and B²_t are compact and nonempty; the paper's argmin fixes no tie-breaking rule
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
--   - encoding: B²_t = {ν : ‖ν − µ̂_t‖_{2,A_t} ≤ √β_t} → (ν − µ̂_t)ᵀ A_t (ν − µ̂_t) ≤ β_t; reason: equivalent because β_t ≥ 0
--   - encoding: rounds t = 1, 2, … → sequences indexed by ℕ with only indices t ≥ 1 read; reason: same instances; index 0 is never used
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Theorem 2 (ConfidenceBall2 bullet), p. 5

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_IsStochLinEnv
import Definitions.Def_StochLinOpt_ConfBall2_IsConfBall2Run
import Definitions.Def_StochLinOpt_ConfBall2_regret
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Theorem 2, ConfidenceBall₂ bullet (corrected: T ≥ 2)** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Theorem 2, p. 5: "(Problem
Independent Upper Bound) Recall that βT = max(128n ln T ln(T²/δ), ((8/3) ln(T²/δ))²). Let
0 < δ < 1. We have: ConfidenceBall2: For all sufficiently large T, the cumulative regret RT of
ConfidenceBall2(D,δ) is with high probability at most O∗(n√T) … More precisely,
Prob(∀T, RT ≤ √(8nTβT ln T)) ≥ 1 − δ").

Let `D ⊂ ℝⁿ` be compact and of full rank with a barycentric spanner `b`, let `0 < δ < 1`, and let
`x*` be an optimal decision for `μ`. In the stochastic linear model (losses in `[−1, 1]` with
conditional mean `μ ⬝ x_t` given the history), for every run of ConfidenceBall₂(D, δ) whose
decisions depend only on the history, with probability at least `1 − δ`,
`R_T ≤ √(8nTβ_T ln T)` holds for every `T ≥ 2` simultaneously.

**Formalization Note** At `T = 1` the printed bound is `0` and fails (`n = 1`, `D = [−1/2, 1]`,
`b_1 = 1`, `ℓ_t = x_t/2` give `R_1 = 3/4` on every outcome), so the event quantifies over
`T ≥ 2`; it is uniform in `T`. The argmin of Algorithm 3.1 is any history-measurable joint
minimizer (`IsConfBall2Run`); the model is stated on the observed losses (`IsStochLinEnv`). -/
theorem theorem_2_confidence_ball2_regret {n : ℕ} {D : Set (Fin n → ℝ)} (hD : IsCompact D)
    (hfull : Submodule.span ℝ D = ⊤) {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {μ xstar : Fin n → ℝ}
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℓ : ℕ → Ω → ℝ) (x : ℕ → Ω → Fin n → ℝ) (henv : IsStochLinEnv P μ D ℓ x)
    (hrun : ∀ ω, IsConfBall2Run D b δ (fun t => ℓ t ω) (fun t => x t ω)) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | ∀ T : ℕ, 2 ≤ T →
        regret μ xstar (fun t => x t ω) T ≤ Real.sqrt (8 * n * T * beta n δ T * Real.log T)} := by sorry

end StochLinOpt.ConfBall2
