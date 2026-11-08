-- Prove2me | Theorems.Thm_PureDPQR_lemma_18
-- name    : PureDPQR.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:54.728194+00:00
-- url     : https://prove2.me/theorems/74eedfae-b0ba-4386-8cca-67ac0dfa1ca1
-- title:
--   Lemma 18, p.21 — selection gap of the exponential mechanism: $\max_ia_i-\mathbb E_{i\sim P}a_i\le\log K/\lambda$
-- statement:
--   **Lemma 18** (Selection gap from exponential mechanism). Let $K\ge1$, $a_1,\dots,a_K\in\mathbb R$, $\lambda>0$, and $P(i)=e^{\lambda a_i}/\sum_je^{\lambda a_j}$ on $[K]$. Then
--
--   $$\max_ia_i-\mathbb E_{i\sim P}\,a_i\le\frac{\log K}{\lambda}.$$
--
--   It is applied to each round's softmax selection in the proof of Proposition 21.
--
--   **Formalization Note** The maximum is a supremum over the nonempty finite index set `Fin K`.
--
--   Differences from the source:
--   - reading: [K] for a_i, i ∈ [K] → K ≥ 1; reason: max_i a_i requires a nonempty index set
--   - encoding: 1-based labels [K] → Fin K; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 18, p.21 (PDF p.22)

import Mathlib

namespace PureDPQR

/-- **Lemma 18** (Selection gap from exponential mechanism), p.21 (PDF p.22).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"Let a_i ∈ R for each i ∈ [K]. If P(i) = e^{λa_i} / ∑_j e^{λa_j} on [K] and λ > 0, then
max_i a_i − E_{i∼P} a_i ≤ log K / λ."

**Formalization Note.** Labels are `Fin K` (0-based). The maximum over `[K]` exists only for
`K ≥ 1`, which is stated (`0 < K`); `max_i a_i` is `⨆ i, a i`, a maximum of finitely many reals.
`λ` is written `lam`. -/
theorem lemma_18 {K : ℕ} (hK : 0 < K) (a : Fin K → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    let P : Fin K → ℝ := fun i => Real.exp (lam * a i) / ∑ j, Real.exp (lam * a j)
    (⨆ i, a i) - ∑ i, P i * a i ≤ Real.log K / lam := by sorry

end PureDPQR
