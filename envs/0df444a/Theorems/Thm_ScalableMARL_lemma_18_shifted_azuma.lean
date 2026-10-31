-- Prove2me | Theorems.Thm_ScalableMARL_lemma_18_shifted_azuma
-- name    : ScalableMARL.lemma_18_shifted_azuma
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:34.301624+00:00
-- url     : https://prove2.me/theorems/25867248-d04d-471f-ae2a-010b0325aae3
-- title:
--   Lemma 18 — Azuma–Hoeffding for $\tau$-shifted martingale differences: $|\sum_{k=0}^tX_k|\le\sqrt{2\tau\sum_k\bar X_k^2\log(2\tau/\delta)}$ (corrected: summand $X_k$)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$, let $\tau\ge1$ be an integer and $\delta\in(0,1)$. Let $(X_t)_{t\ge0}$ be real and $\mathcal F_t$-adapted, with
--   $$\mathbb E[X_t\mid\mathcal F_{t-\tau}]=0\quad(t\ge\tau),\qquad\mathbb E[X_t]=0\quad(t<\tau),$$
--   and $|X_t|\le\bar X_t$ almost surely for deterministic constants $\bar X_t$. Then for every $t$, with probability at least $1-\delta$,
--   $$\Big|\sum_{k=0}^{t}X_k\Big|\le\sqrt{2\tau\sum_{k=0}^{t}\bar X_k^2\,\log\frac{2\tau}{\delta}} .$$
--
--   For $\tau=1$ this is the Azuma–Hoeffding inequality for bounded martingale differences. In the paper it handles the critic's noise, whose conditional mean vanishes only given the information $\tau$ steps back (Lemma 10).
--
--   **Formalization Note** "With probability $1-\delta$" is $\mathbb P(\cdot)\ge1-\delta$. For $t<\tau$ the σ-algebra $\mathcal F_{t-\tau}$ is read as the trivial one.
--
--   Differences from the source:
--   - correction: |Σ_{k=0}^t X_t| (the summand does not depend on k) → |Σ_{k=0}^t X_k|; reason: the printed statement is false: for τ = 1 and i.i.d. Rademacher X_t with X̄_t = 1, |Σ_{k=0}^t X_t| = t + 1 surely, which exceeds √(2(t+1) log(2/δ)) once t + 1 > 2 log(2/δ); the proof bounds Σ_k X_k
--   - reading: F_{t−τ} for t < τ → the trivial σ-algebra, i.e. E[X_t] = 0; reason: the proof's subsequences Y^ℓ_k = X_{τk+ℓ} start with E[Y^ℓ_0] = 0
--   - reading: X̄_t → deterministic constants; reason: the proof treats them as scalars Ȳ^ℓ_k
--   - encoding: δ and τ unqualified → δ ∈ (0, 1), τ ≥ 1 an integer; reason: log(2τ/δ) and the τ-shift presuppose them
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 34, Lemma 18

import Mathlib

namespace ScalableMARL

open MeasureTheory

/-- **Lemma 18 (Azuma–Hoeffding for a τ-shifted martingale difference sequence).** Qu, Wierman &
Li, arXiv:1912.02906v3, p. 34, Lemma 18. Let `X_t` be an `F_t`-adapted process with
`E[X_t | F_{t−τ}] = 0` and `|X_t| ≤ X̄_t` almost surely. Then with probability at least `1 − δ`,
`|Σ_{k=0}^t X_k| ≤ √(2τ Σ_{k=0}^t X̄_k² log(2τ/δ))`.

**Formalization Note.** The printed summand `X_t` is a typo for `X_k` (as the proof shows). For
`t < τ`, `F_{t−τ}` is the trivial σ-algebra, so the condition reads `E[X_t] = 0`. The bounds
`X̄_t` are deterministic constants (so the `X_t` are integrable), `τ ≥ 1` is an integer and
`δ ∈ (0, 1)`. The bound holds for every `t`. -/
theorem lemma_18_shifted_azuma {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (Xbar : ℕ → ℝ) (τ : ℕ)
    (hτ : 1 ≤ τ) (hadapt : Adapted ℱ X)
    (hmd : ∀ t, τ ≤ t → μ[X t | ℱ (t - τ)] =ᵐ[μ] 0)
    (hmd0 : ∀ t, t < τ → ∫ ω, X t ω ∂μ = 0)
    (hbd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ Xbar t) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (t : ℕ) :
    ENNReal.ofReal (1 - δ) ≤
      μ {ω | |∑ k ∈ Finset.range (t + 1), X k ω| ≤
        Real.sqrt (2 * τ * (∑ k ∈ Finset.range (t + 1), Xbar k ^ 2) * Real.log (2 * τ / δ))} := by sorry

end ScalableMARL
