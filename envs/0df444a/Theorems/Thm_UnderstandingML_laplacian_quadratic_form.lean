-- Prove2me | Theorems.Thm_UnderstandingML_laplacian_quadratic_form
-- name    : UnderstandingML.laplacian_quadratic_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:17:38.560066+00:00
-- url     : https://prove2.me/theorems/84feee0f-000f-4487-99cc-e91d74457905
-- title:
--   Proof of Lemma 22.3: for symmetric W, vᵀLv = ½ ∑_{r,s} W_{r,s}(v_r − v_s)² for the unnormalized graph Laplacian L = D − W
-- statement:
--   **From the proof of Lemma 22.3.** For any vector $v$,
--   $$v^\top L v = \tfrac12\Big(\sum_r D_{r,r}v_r^2 - 2\sum_{r,s}v_r v_s W_{r,s} + \sum_s D_{s,s}v_s^2\Big) = \tfrac12\sum_{r,s}W_{r,s}(v_r - v_s)^2.$$
--
--   Formally: for a symmetric $W \in \mathbb{R}^{m \times m}$, $L = D - W$ and every $v \in \mathbb{R}^m$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22.3.2 p. 316, the identity in the proof of Lemma 22.3

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML

/-- **The Laplacian quadratic form** (proof of Lemma 22.3, p. 316): for a symmetric similarity
matrix `W` and every vector `v`, `vᵀ L v = ½ ∑_{r,s} W_{r,s} (v_r − v_s)²`. -/
theorem laplacian_quadratic_form {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.IsSymm)
    (v : Fin m → ℝ) :
    dotProduct v ((laplacian W).mulVec v) = 1 / 2 * ∑ r, ∑ s, W r s * (v r - v s) ^ 2 := by sorry

end UnderstandingML
