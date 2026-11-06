-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_7_8
-- name    : SparseSDP.TwoSided.lemma_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:11.649459+00:00
-- url     : https://prove2.me/theorems/0edb1632-e584-4758-beeb-ef15661309df
-- title:
--   Lemma 7.8, p. 54 — exponential weights with clipped stochastic feedback
-- statement:
--   Let $(\mathcal G_t)$ be a filtration. Let $c_t\in\mathbb R^m$ be the true payoff vector on round $t$ and let $\hat p_t$ be the exponential-weights distribution, initialized uniformly, from the feedback $\hat c_1,\dots,\hat c_{t-1}$ with learning rate $\eta_y>0$. Assume $\hat c_t$ is $\mathcal G_t$-measurable, $c_t$ is $\mathcal G_{t-1}$-measurable and, for every $j$:
--
--   1. $|[\hat c_t]_j|\le B$;
--   2. $\mathbb E[[\hat c_t]_j^2\mid\mathcal G_{t-1}]\le\sigma^2$;
--   3. $|\mathbb E[[\hat c_t]_j\mid\mathcal G_{t-1}]-[c_t]_j|\le b$.
--
--   Let $\Lambda_F=\log(4(m+1)/\delta_F)$. If $\eta_yB\le1$, then for every $\delta_F\in(0,1)$, with probability at least $1-\delta_F$,
--   $$
--   \sum_{t=1}^T\langle c_t,\hat p_t\rangle-\min_{j\in[m]}\sum_{t=1}^T[c_t]_j\le O\Big(\frac{\log(2m)}{\eta_y}+\eta_y\sigma^2T+\sigma\sqrt{T\Lambda_F}+B\Lambda_F+bT\Big).
--   $$
--
--   The update tolerates noisy biased feedback, at a price set by its range, second moment and bias.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ → a universal constant $C$ chosen before everything else; reason: the meaning of $O$ here
--   - reading: the conditions on the feedback → almost sure bounds with $\sigma,b\ge0$; reason: conditional expectations are defined almost surely
--   - encoding: $\hat p_t$ is $\mathcal G_{t-1}$-measurable → omitted as a hypothesis; reason: it is a function of $\hat c_1,\dots,\hat c_{t-1}$, so it follows
--   - encoding: a filtration $(\mathcal G_t)_{t=0}^T$ → a filtration on $\mathbb N$, used for $t\le T$; reason: any finite filtration extends by a constant
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under $\mu$; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 7.8, p. 54, Eq. (285)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Prog

open MeasureTheory Matrix

namespace SparseSDP.TwoSided

/-- **Lemma 7.8** (Exponential Weights with Clipped Stochastic Feedback), p. 54.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 7.8, p. 54.

`O(·)` is a universal constant `C`, chosen before everything else. The range, second-moment and
bias conditions hold almost surely, for `1 ≤ t ≤ T`. `p̂_t` is a function of `ĉ₁, …, ĉ_{t−1}`, so its
`𝒢_{t−1}`-measurability follows from that of the feedback. -/
theorem lemma_7_8 : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝒢 : Filtration ℕ mΩ) (T m : ℕ) [NeZero m] (c chat : ℕ → Ω → Vec m)
      (B σ b ηy δF : ℝ), 0 ≤ B → 0 ≤ σ → 0 ≤ b → 0 < ηy → ηy * B ≤ 1 → 0 < δF → δF < 1 →
      (∀ t ∈ Finset.Icc 1 T, ∀ j, Measurable[𝒢 t] fun w => chat t w j) →
      (∀ t ∈ Finset.Icc 1 T, ∀ j, Measurable[𝒢 (t - 1)] fun w => c t w j) →
      (∀ t ∈ Finset.Icc 1 T, ∀ j, ∀ᵐ w ∂μ, |chat t w j| ≤ B) →
      (∀ t ∈ Finset.Icc 1 T, ∀ j, ∀ᵐ w ∂μ,
        (μ[fun w' => chat t w' j ^ 2 | 𝒢 (t - 1)]) w ≤ σ ^ 2) →
      (∀ t ∈ Finset.Icc 1 T, ∀ j, ∀ᵐ w ∂μ,
        |(μ[fun w' => chat t w' j | 𝒢 (t - 1)]) w - c t w j| ≤ b) →
      μ {w | ¬ ∑ t ∈ Finset.Icc 1 T, (c t w ⬝ᵥ expWeights ηy (fun τ => chat τ w) t) -
            minOver (fun j => ∑ t ∈ Finset.Icc 1 T, c t w j) ≤
          C * (Real.log (2 * m) / ηy + ηy * σ ^ 2 * T +
            σ * √(T * Real.log (4 * (m + 1) / δF)) +
            B * Real.log (4 * (m + 1) / δF) + b * T)} ≤ ENNReal.ofReal δF := by sorry

end SparseSDP.TwoSided
