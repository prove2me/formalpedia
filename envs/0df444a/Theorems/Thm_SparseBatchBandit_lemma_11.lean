-- Prove2me | Theorems.Thm_SparseBatchBandit_lemma_11
-- name    : SparseBatchBandit.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:05.660444+00:00
-- url     : https://prove2.me/theorems/ff46c8a0-169f-4c56-bdcd-849615791b57
-- title:
--   Lemma 11, p.22 — sub-Gaussian maximal inequality
-- statement:
--   Let $X_1,\dots,X_K$ be centered $\sigma^2$-sub-Gaussian random variables, with no independence assumed. Then for any $t>0$,
--
--   $$
--   \mathbb P\Big(\max_{k\in[K]}X_k\ge t\Big)\le Ke^{-t^2/(2\sigma^2)} .
--   $$
--
--   This is the tail bound behind the per-round regret bound.
--
--   Differences from the source:
--   - encoding: X₁, …, X_K centered σ²-sub-Gaussian → HasSubgaussianMGF (X k) (σ²), with K ≠ 0 and σ > 0; reason: the MGF bound implies centered; a maximum needs an arm
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Lemma 11, p.22

import Mathlib
import Definitions.Def_SparseBatchBandit_maxArm
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SparseBatchBandit

/-- **Lemma 11** (Sub-Gaussian maximal inequality), Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.22 (PDF 22): if `X₁, …, X_K` are centered
`σ²`-sub-Gaussian random variables, then for any `t > 0`,
`P(max_{k∈[K]} X_k ≥ t) ≤ K e^{−t²/(2σ²)}`. No independence is assumed.

**Formalization Note.** `HasSubgaussianMGF` implies that the `X_k` are centered. -/
theorem lemma_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (X : Fin K → Ω → ℝ) (σ : ℝ≥0) (_hσ : 0 < σ)
    (_hX : ∀ k, HasSubgaussianMGF (X k) (σ ^ 2) P) (t : ℝ) (_ht : 0 < t) :
    P.real {ω | t ≤ maxArm (fun k => X k ω)} ≤
      (K : ℝ) * Real.exp (-t ^ 2 / (2 * (σ : ℝ) ^ 2)) := by sorry

end SparseBatchBandit
