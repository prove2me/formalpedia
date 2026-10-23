-- Prove2me | Theorems.Thm_SubsetShrink_Events_prob_F
-- name    : SubsetShrink.Events.prob_F
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:27.072982+00:00
-- url     : https://prove2.me/theorems/c41e85de-7f19-42de-8a5f-78d12139f380
-- title:
--   Theorem 1 (𝓕 part), p. 13; B.1, p. 38 — P(𝓕) ≥ 1 − δ₀/2 (Bellec–Lecué–Tsybakov, Thm 4.1)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$ and $\delta_0\in(0,1]$, and let $\epsilon$ have independent $N(0,\sigma^2)$ coordinates. Then the event
--   $$\mathcal F = \Bigl\{\epsilon^\top X u \le [4+\sqrt2]\,\sigma\max\Bigl(\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)},\ \sqrt{\log(1/\delta_0)}\,\|Xu\|\Bigr),\ \forall u\in\mathbb R^p\Bigr\}$$
--   is measurable and
--   $$\mathbb P(\mathcal F)\ge 1-\delta_0/2 .$$
--
--   The paper takes this bound from Theorem 4.1 of Bellec, Lecué and Tsybakov (*Slope meets Lasso*, 2018). It is the probabilistic input for the $\ell_1$ and $\ell_2$ slow-rate bounds, and it implies the bound for $\mathcal E_s$.
--
--   **Formalization Note** The probability space is $\mathbb R^n$ with the product law $N(0,\sigma^2)^{\otimes n}$ of $\epsilon$; $\mathcal F$ is a set of noise vectors. Measurability is part of the conclusion, not a hypothesis. The sorted sum is the definition `sortedSum` (a maximum over permutations, equal to the paper's sum by the rearrangement inequality).
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 13, Theorem 1 (P(F) ≥ 1 − δ0/2); proof B.1, p. 38, first sentence (Theorem 4.1 in [5])

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem prob_F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    MeasurableSet (F X σ δ0) ∧ 1 - δ0 / 2 ≤ (noiseLaw n σ (F X σ δ0)).toReal := by sorry
end SubsetShrink.Events
