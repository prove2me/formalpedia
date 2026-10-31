-- Prove2me | Theorems.Thm_ShapleyNV_lemma_EC_2
-- name    : ShapleyNV.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:59.863574+00:00
-- url     : https://prove2.me/theorems/fe4df300-f3cf-46e8-8125-0f3ac6a08c78
-- title:
--   Lemma EC.2, p.ec3 — $A^+ = A^-$: the matrix $(A_{jk}(x))$ has a saddle point
-- statement:
--   With the notation of Lemma 1 (distinct observed features $\hat x_k$, an in-sample policy $\hat f \ge 0$, and the interpolation matrix $A_{jk}(x)$ of (S)), for every $x \in \mathcal X$,
--
--   $$
--   A^+(x) := \min_{j} \max_{k} A_{jk}(x) = \max_{k} \min_{j} A_{jk}(x) =: A^-(x).
--   $$
--
--   So the minimax matrix saddle point in Theorem 1 (II) exists, and the two formulas for the Shapley policy agree.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.2, p.ec3 (PDF 24)

import Mathlib
import Definitions.Def_ShapleyNV_shapley
import Definitions.Def_ShapleyNV_shapleyLower

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma EC.2**, p.ec3: with the notation of Lemma 1, `A⁺ = A⁻`, i.e. the matrix `(A_jk(x))_jk`
has a saddle point at every `x`: `min_j max_k A_jk(x) = max_k min_j A_jk(x)`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.2, p.ec3 (PDF 24). -/
theorem lemma_EC_2 {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∀ x, shapley D y x = shapleyLower D y x := by sorry

end ShapleyNV
