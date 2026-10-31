-- Prove2me | Theorems.Thm_ShapleyNV_lemma_1_ii
-- name    : ShapleyNV.lemma_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:54:09.897983+00:00
-- url     : https://prove2.me/theorems/0a2bd1a0-79c2-4847-a46e-060ef83f191c
-- title:
--   Lemma 1 (ii), (5), p.8 — optimality: $\sup_x\{\Phi(f(x))-\|x-\hat x_k\|\}\le\max_j\{\Phi(\hat f(\hat x_j))-\|\hat x_j-\hat x_k\|\}$
-- statement:
--   With the notation of Lemma 1, for every $k \in [K]$ and every convex function $\Phi : \mathbb R \to \mathbb R$,
--
--   $$
--   \sup_{x \in \mathcal X} \big\{ \Phi(f(x)) - \|x - \hat x_k\| \big\} \le \max_{j=1,\dots,K} \big\{ \Phi(\hat f(\hat x_j)) - \|\hat x_j - \hat x_k\| \big\}. \tag{5}
--   $$
--
--   This is the key property behind the optimality of the Shapley extension: with $\Phi = \Psi(\cdot, z)/\lambda$ it shows that extending $\hat f$ does not increase the dual objective.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: sup over x ∈ 𝒳 of the left side → the inequality for every x ∈ X; reason: the right side does not depend on x
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma 1 (ii), eq. (5), p.8

import Mathlib
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma 1 (ii) [Optimality]**, (5), p.8: for all `k ∈ [K]` and every convex `Φ : ℝ → ℝ`,
`sup_{x∈𝒳} { Φ(f(x)) − ‖x − x̂_k‖ } ≤ max_j { Φ(f̂(x̂_j)) − ‖x̂_j − x̂_k‖ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma 1 (ii), eq. (5), p.8.

**Formalization Note.** The supremum over `x` is written as the inequality for every `x` (the right
side does not depend on `x`). -/
theorem lemma_1_ii {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) (k : Fin D.K) (x : X) :
    Φ (shapley D y x) - dist x (D.xhat k) ≤
      Finset.univ.sup' D.univ_nonempty (fun j => Φ (y j) - dist (D.xhat j) (D.xhat k)) := by sorry

end ShapleyNV
