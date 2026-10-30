-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_lemma_13_martingale_difference
-- name    : StochLinOpt.ConfBall2.lemma_13_martingale_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:57:04.476913+00:00
-- url     : https://prove2.me/theorems/cacecb55-baf1-4c36-9967-c39be49bc5e8
-- title:
--   Lemma 13: $M_t$ is a martingale difference sequence for $(\mathcal H_t)$
-- statement:
--   Assume the stochastic linear model on $(\Omega,P)$ with decision set $D$ spanning $\mathbb R^n$, barycentric spanner $b$, and any parameter $\delta$. Let
--
--   $$M_t=2\,\eta_t\,E_t\,\frac{x_t^\top(\widehat\mu_t-\mu)}{1+w_t^2}.$$
--
--   Then for every round $t\ge1$:
--
--   1. $M_t$ is $\mathcal H_{t+1}$-measurable;
--   2. $M_t$ is integrable;
--   3. $\mathbb E(M_t\mid\mathcal H_t)=0$ almost surely.
--
--   That is, $(M_t)$ is a martingale difference sequence with respect to the histories $\mathcal H_t=\sigma(\ell_1,\dots,\ell_{t-1})$. Its partial sums are the martingale whose concentration (Lemma 14) drives the confidence bound.
--
--   Differences from the source:
--   - encoding: M_t is a martingale difference sequence with respect to H_t → M_t is H_{t+1}-measurable, integrable, and E(M_t | H_t) = 0 a.s., for every t ≥ 1; reason: the definition of a martingale difference sequence, spelled out
--   - generalization: M_t built from the run of ConfidenceBall2(D, δ) → any decisions satisfying the model (no argmin rule needed) and any δ; reason: the proof uses only that x_t, µ̂_t, E_t are determined by H_t and E(η_t | H_t) = 0
--   - generalization: E(c_t(x) | H_t) = μ·x for all x ∈ D, ℓ_t = c_t(x_t) ∈ [−1, 1] → losses ℓ_t ∈ [−1, 1], x_t H_t-measurable, E(ℓ_t | H_t) = μ·x_t a.s. (IsStochLinEnv); reason: the paper's assumption implies the loss-level one because x_t is determined by H_t (proof of Lemma 13, p. 9); the analysis uses only the latter
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 13, p. 9

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_IsStochLinEnv
import Definitions.Def_StochLinOpt_ConfBall2_martM
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Lemma 13** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 13, p. 9: "Define a random variable Mt by
Mt = 2ηtEt x†t(µ̂t − µ)/(1 + w2t). Then Mt is a martingale difference sequence with respect to
the sequence of game histories Ht").

In the stochastic linear model, for every round `t ≥ 1` the random variable
`M_t = 2 η_t E_t x_tᵀ(µ̂_t − μ)/(1 + w_t²)` is `H_{t+1}`-measurable, integrable, and satisfies
`E(M_t | H_t) = 0` almost surely, where `H_t = σ(ℓ_1, …, ℓ_{t−1})`.

**Formalization Note** "Martingale difference sequence with respect to `H_t`" is spelled out as
these three properties. The lemma uses only the model (`IsStochLinEnv`: `x_t` is
`H_t`-measurable and `E(ℓ_t | H_t) = μ ⬝ x_t`), not the algorithm's argmin rule, and holds for
every `δ`. -/
theorem lemma_13_martingale_difference {n : ℕ} {D : Set (Fin n → ℝ)} (hfull : Submodule.span ℝ D = ⊤)
    {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b) (δ : ℝ) {μ : Fin n → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℓ : ℕ → Ω → ℝ) (x : ℕ → Ω → Fin n → ℝ) (henv : IsStochLinEnv P μ D ℓ x) (t : ℕ)
    (ht : 1 ≤ t) :
    Measurable[lossHistory ℓ (t + 1)]
        (fun ω => martM b (fun s => x s ω) (fun s => ℓ s ω) μ δ t) ∧
      Integrable (fun ω => martM b (fun s => x s ω) (fun s => ℓ s ω) μ δ t) P ∧
      P[fun ω => martM b (fun s => x s ω) (fun s => ℓ s ω) μ δ t | lossHistory ℓ t] =ᵐ[P] 0 := by sorry

end StochLinOpt.ConfBall2
