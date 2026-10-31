-- Prove2me | Theorems.Thm_ShapleyNV_lemma_1_i
-- name    : ShapleyNV.lemma_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:39.439995+00:00
-- url     : https://prove2.me/theorems/06b87df9-71cb-470a-8a56-c28d7a14297d
-- title:
--   Lemma 1 (i), p.8 — the Shapley extension interpolates: $f(\hat x_k) = \hat f(\hat x_k)$
-- statement:
--   Let $\hat x_1, \dots, \hat x_K$ be distinct points of the feature space $\mathcal X$ and let $\hat f$ assign an order quantity $\hat f(\hat x_k) \ge 0$ to each of them. Let $f$ be the Shapley extension of $\hat f$,
--
--   $$
--   f(x) = \min_{j} \max_{k} A_{jk}(x),
--   $$
--
--   with $A_{jk}$ the inverse-distance interpolation matrix (S) and $A_{kk} = \hat f(\hat x_k)$. Then
--
--   $$
--   f(\hat x_k) = \hat f(\hat x_k) \qquad \text{for all } k \in [K].
--   $$
--
--   So $f$ is an extension of $\hat f$ from the observed features to all of $\mathcal X$.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma 1 (i), p.8

import Mathlib
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma 1 (i) [Extension]**, p.8: `f(x̂_k) = f̂(x̂_k)` for all `k ∈ [K]`, where `f` is the
Shapley extension (S) of the in-sample policy `f̂` (here `y k = f̂(x̂_k)`).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma 1 (i), p.8.

**Formalization Note.** The feature space is any metric space (the paper's `𝒳 ⊂ (ℝ^d, ‖·‖)` is an
instance); `f` is `shapley D y = min_j max_k A_jk`. -/
theorem lemma_1_i {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∀ k, shapley D y (D.xhat k) = y k := by sorry

end ShapleyNV
