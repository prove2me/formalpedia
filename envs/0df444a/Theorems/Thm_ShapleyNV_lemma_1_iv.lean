-- Prove2me | Theorems.Thm_ShapleyNV_lemma_1_iv
-- name    : ShapleyNV.lemma_1_iv
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:45.554012+00:00
-- url     : https://prove2.me/theorems/33f6295d-2f96-4b53-acbc-0c5c0d3a7e87
-- title:
--   Lemma 1 (iv), p.8 — $\|f\|_{\mathrm{Lip}} \le \max_{j\ne k} |\hat f(\hat x_j)-\hat f(\hat x_k)|/\|\hat x_j-\hat x_k\|$
-- statement:
--   With the notation of Lemma 1, the Lipschitz norm of the Shapley extension $f$ is bounded by the discrete Lipschitz constant of the data:
--
--   $$
--   \|f\|_{\mathrm{Lip}} \le \max_{j \ne k} \frac{|\hat f(\hat x_j) - \hat f(\hat x_k)|}{\|\hat x_j - \hat x_k\|}.
--   $$
--
--   Equivalently: every $L \ge 0$ with $|\hat f(\hat x_j) - \hat f(\hat x_k)| \le L\,\|\hat x_j - \hat x_k\|$ for all $j \ne k$ is a Lipschitz constant of $f$ on $\mathcal X$.
--
--   In particular the extension is continuous, hence measurable.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: ‖f‖_Lip ≤ max_{j≠k} |f̂(x̂_j) − f̂(x̂_k)| / ‖x̂_j − x̂_k‖ → every L ≥ 0 bounding all pairwise slopes is a Lipschitz constant of f; reason: equivalent (take L equal to the maximum); it also covers K = 1, where the maximum is over an empty set
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma 1 (iv), p.8

import Mathlib
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma 1 (iv) [Lipschitzness]**, p.8: the Lipschitz norm of `f` is at most
`max_{j≠k} |f̂(x̂_j) − f̂(x̂_k)| / ‖x̂_j − x̂_k‖`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma 1 (iv), p.8.

**Formalization Note.** Stated as: every `L ≥ 0` with `|y_j − y_k| ≤ L ‖x̂_j − x̂_k‖` for all
`j ≠ k` is a Lipschitz constant of `f`. Taking `L` equal to the maximum gives the paper's bound,
and conversely; for `K = 1` (empty maximum) it says `f` is constant. -/
theorem lemma_1_iv {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k)
    (L : ℝ≥0) (hL : ∀ j k, j ≠ k → |y j - y k| ≤ L * dist (D.xhat j) (D.xhat k)) :
    LipschitzWith L (shapley D y) := by sorry

end ShapleyNV
