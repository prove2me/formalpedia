-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_Supplement_lemma_19
-- name    : SampleDrivenOS.Structure.Supplement.lemma_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:52:37.81482+00:00
-- url     : https://prove2.me/theorems/dcba15e1-29a5-4bd5-8788-c51924017413
-- title:
--   Lemma 19 — two-sided cumulative offline coefficient comparison
-- statement:
--   Let N,h,k be integers with p=h/N∈(0,1), N≥1/(1−p)+1 and 1≤k≤h+1. Define
--   $$
--   C_k=\sum_{j=1}^k\frac{N-h}{N-j+1}\prod_{s=0}^{j-2}\frac{h-s}{N-s}.
--   $$
--   Then
--   $$
--   1\le\frac{C_k}{1-p^k}\le1+\frac{e}{(1-p)(N-1)}.
--   $$
--   The empty product at j=1 is 1. Both bounds, the full k-range and the printed size hypothesis are retained.
--
--   This support for Theorem 13 compares the offline masses in the finite dependent experiment with their geometric limits. Its grid premise belongs to this lemma and does not restrict Theorem 13's domain.
--
--   Differences from the source:
--   - encoding: integer N,h,k satisfying the printed positive-domain premises → natural N,h,k and a product over range(j−1); reason: the premises already force these integers positive and make the printed j=1 product empty
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 39, Lemma 19

import Definitions.Def_SampleDrivenOS_Structure_Supplement_FiniteLP

namespace SampleDrivenOS.Structure.Supplement

theorem lemma_19 (N h k : ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hgrid : p = (h : ℝ) / (N : ℝ)) (hN : 1 / (1 - p) + 1 ≤ (N : ℝ))
    (hk : 1 ≤ k ∧ k ≤ h + 1) :
    1 ≤ cumulativeOffline N h k / (1 - p ^ k) ∧
    cumulativeOffline N h k / (1 - p ^ k) ≤
      1 + Real.exp 1 / ((1 - p) * ((N : ℝ) - 1)) := by sorry

end SampleDrivenOS.Structure.Supplement
