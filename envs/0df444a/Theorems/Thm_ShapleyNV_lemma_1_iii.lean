-- Prove2me | Theorems.Thm_ShapleyNV_lemma_1_iii
-- name    : ShapleyNV.lemma_1_iii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:46.825982+00:00
-- url     : https://prove2.me/theorems/cbdf5ce1-9aec-4a7c-bea8-f78ad75c5884
-- title:
--   Lemma 1 (iii), p.8 — boundedness: $\min_k \hat f(\hat x_k) \le f \le \max_k \hat f(\hat x_k)$
-- statement:
--   With the notation of Lemma 1 (distinct observed features $\hat x_k$, an in-sample policy $\hat f \ge 0$, and its Shapley extension $f$), for every $x \in \mathcal X$,
--
--   $$
--   \min_{k \in [K]} \hat f(\hat x_k) \le f(x) \le \max_{k \in [K]} \hat f(\hat x_k).
--   $$
--
--   The extension never orders less than the smallest or more than the largest in-sample order.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma 1 (iii), p.8

import Mathlib
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma 1 (iii) [Boundedness]**, p.8: `min_k f̂(x̂_k) ≤ f ≤ max_k f̂(x̂_k)`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma 1 (iii), p.8. -/
theorem lemma_1_iii {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∀ x, Finset.univ.inf' D.univ_nonempty y ≤ shapley D y x ∧
      shapley D y x ≤ Finset.univ.sup' D.univ_nonempty y := by sorry

end ShapleyNV
