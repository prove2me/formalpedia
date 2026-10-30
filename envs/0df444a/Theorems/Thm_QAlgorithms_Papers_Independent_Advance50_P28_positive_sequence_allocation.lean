-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_positive_sequence_allocation
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.positive_sequence_allocation
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:49:00.751991+00:00
-- url     : https://prove2.me/theorems/9a9751f3-0913-4734-af02-52a152fa3edb
-- title:
--   Lemma 3 (47)
-- statement:
--   Let $M\ge N\ge1$ be integers. Let $\alpha_1,\ldots,\alpha_N$ and $\beta_1,\ldots,\beta_M$ be strictly positive real sequences, without normalization, such that $\sum_i\alpha_i\ge\sum_j\beta_j$. There is a map $f:\{1,\ldots,M\}\to\{1,\ldots,N\}$ such that
--   $$\sum_{i=1}^N\left[\sum_{j:f(j)=i}\beta_j-\alpha_i\right]_+\le N\max_j\beta_j.$$
--   Here $[x]_+=\max(x,0)$. This allocation result supports the construction of finite extractors.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 8, Lemma 3 (47)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.8, Lemma 3, (47): positive, unnormalized sequences. -/
theorem positive_sequence_allocation {M N : ℕ} (hN : 0 < N) (hMN : N ≤ M)
    (alpha : Fin N → ℝ) (beta : Fin M → ℝ)
    (ha : ∀ i, 0 < alpha i) (hb : ∀ j, 0 < beta j)
    (hmass : (∑ j, beta j) ≤ ∑ i, alpha i) :
    ∃ f : Fin M → Fin N,
      (∑ i, max ((∑ j, if f j = i then beta j else 0) - alpha i) 0) ≤
        (N : ℝ) * peak beta := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
