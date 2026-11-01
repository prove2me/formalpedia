-- Prove2me | Theorems.Thm_StochCoordProx_lemma_6_aligned_count
-- name    : StochCoordProx.lemma_6_aligned_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:25.42752+00:00
-- url     : https://prove2.me/theorems/abbe5fcb-fa13-45cb-a911-3e9f02e74272
-- title:
--   Lemma 6 — $P[|\mathbb A_K|\ge(1-\beta)(1-\delta)(K+1)]\ge1-e^{-\frac{\beta^2}{2}(1-\delta)(K+1)}$
-- statement:
--   Let $(\Omega,P)$ be a probability space with a filtration $(\mathcal F_k)$, let $\delta\in(0,1)$, and let the events $W_k$ ("$U_k$ is well-aligned") satisfy Assumption 2: $W_k$ is $\mathcal F_{k+1}$-measurable and $P[W_k\mid\mathcal F_k]\ge1-\delta$ almost surely. Let $|\mathbb A_K|$ be the number of $k\in\{0,\dots,K\}$ with $W_k$. Then for every $K\ge0$ and every $\beta\in(0,1)$
--
--   $$
--   P\bigl[|\mathbb A_K|\ge(1-\beta)(1-\delta)(K+1)\bigr]\ge1-e^{-\frac{\beta^2}{2}(1-\delta)(K+1)},
--   $$
--
--   stated equivalently as
--
--   $$
--   P\bigl[|\mathbb A_K|<(1-\beta)(1-\delta)(K+1)\bigr]\le e^{-\frac{\beta^2}{2}(1-\delta)(K+1)} .
--   $$
--
--   With high probability, a fixed fraction of the first $K+1$ iterations is well-aligned. This is the probabilistic input of Theorem 1.
--
--   **Formalization Note** The bad-event form is used. For a non-measurable set Lean's measure is the outer measure, which makes this the strong form.
--
--   Differences from the source:
--   - generalization: the events {U_k well-aligned} of an SCPG run, under Assumptions 1 and 2 → any events W_k satisfying Assumption2 for some filtration; Assumption 1 not assumed; reason: the SCPG alignment events are an instance; Assumption 1 is not used
--   - reading: well-aligned with probability at least 1 − δ, independently of the filtration 𝓕_k := {U₀,…,U_{k−1}} → P[W_k | 𝓕_k] ≥ 1 − δ almost surely; reason: alignment of U_k is measured at x_k, which depends on the past; the reading in which the event is independent of 𝓕_k implies this one
--   - generalization: the filtration 𝓕_k = σ(U₀,…,U_{k−1}) → any filtration with W_k ∈ 𝓕_{k+1}; reason: the paper's filtration is an instance whenever the iterates are measurable
--   - encoding: measurability of the events (implicit) → W_k is 𝓕_{k+1}-measurable; reason: without it P[W_k | 𝓕_k] and the probability in (20) are undefined
--   - encoding: P[|𝔸_K| ≥ (1−β)(1−δ)(K+1)] ≥ 1 − e^{…} → P[|𝔸_K| < (1−β)(1−δ)(K+1)] ≤ e^{…}; reason: the same for measurable events; with the outer measure the bad-event form is the stronger
--   - generalization: the set 𝒰 bounded (standing assumption, p.4); 𝓛_F(x₀) bounded (standing assumption, p.7: "Throughout the paper, we also assume boundedness of the level set") → not assumed; reason: the proof does not use them; they serve only to make H_{F,max} finite, which this statement does not involve; every instance satisfying them is covered
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Lemma 6, display (20), p.10

import Mathlib
import Definitions.Def_StochCoordProx_Assumption2
import Definitions.Def_StochCoordProx_alignedCount

open MeasureTheory

namespace StochCoordProx

/-- **Lemma 6 (number of well-aligned iterations).** Let `(Ω, P)` be a probability space with a
filtration `𝓕`, and let `W k` (the event "`U_k` is well-aligned") satisfy Assumption 2 with
`δ ∈ (0,1)`. Then for every `K ≥ 0` and every `β ∈ (0,1)`,
`P[|𝔸_K| ≥ (1 − β)(1 − δ)(K + 1)] ≥ 1 − e^{−(β²/2)(1−δ)(K+1)}`  (20),
stated as the bound on the complementary event
`P[|𝔸_K| < (1 − β)(1 − δ)(K + 1)] ≤ e^{−(β²/2)(1−δ)(K+1)}`.

Necoara & Chorobura, arXiv:2104.13370v3, Lemma 6, display (20), p.10.

**Formalization Note.** The events are abstract: any adapted events satisfying Assumption 2;
the SCPG alignment events are the instance. `|𝔸_K|(ω)` is `alignedCount W K ω`, the number of
`k ∈ {0, …, K}` with `ω ∈ W k`. The bad-event form is used (Mathlib's measure of a possibly
non-measurable set is its outer measure, which makes this the strong form). -/
theorem lemma_6_aligned_count {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℕ m0) (W : ℕ → Set Ω) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hA2 : Assumption2 P 𝓕 W δ) (K : ℕ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    P {ω | (alignedCount W K ω : ℝ) < (1 - β) * (1 - δ) * (K + 1)} ≤
      ENNReal.ofReal (Real.exp (-(β ^ 2 / 2) * (1 - δ) * (K + 1))) := by sorry

end StochCoordProx
