-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_1_8
-- name    : SmoothedSimplex.TwoPhase.lemma_5_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:17.222263+00:00
-- url     : https://prove2.me/theorems/506cf242-53ad-4311-b589-b11e80aec84f
-- title:
--   Lemma 5.1.8 (Sum over K and j of Y^j_K)
-- statement:
--   Under the same independent Gaussian model with $n>d\ge3$ and center norms at most one, the total number of low-height events over all $(d-1)$-sets obeys
--   $$\Pr\!\left[\sum_{K\in\binom{[n]}{d-1}}\sum_{j\notin K}Y_K^j>\left\lceil\frac{n-d-1}{2}\right\rceil\binom n{d-1}\right]\le n^{-n+d-1}.$$
--   This concentration bound is one component of the many-good-choices estimate.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.1.8, printed p. 63, PDF p. 63

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.1.8 (Sum over K and j of Y^j_K), printed p. 63, PDF p. 63, under all conditions of Lemma 5.1.1. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem lemma_5_1_8 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (hc : ∀ i, ‖c i‖ ≤ 1) (σ : ℝ) (hσ : 0 < σ) :
    ((gaussianFamily c σ) {a |
      (∑ K ∈ Finset.univ.powersetCard (d - 1),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ∉ K), lowHeight a K j σ) >
        Nat.ceil (((n : ℝ) - d - 1) / 2) * Nat.choose n (d - 1)}).toReal ≤
      (n : ℝ) ^ (-(n : ℝ) + d - 1 : ℝ) := by sorry

end SmoothedSimplex.TwoPhase
