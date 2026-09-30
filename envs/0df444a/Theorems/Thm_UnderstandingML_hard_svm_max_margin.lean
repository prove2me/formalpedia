-- Prove2me | Theorems.Thm_UnderstandingML_hard_svm_max_margin
-- name    : UnderstandingML.hard_svm_max_margin
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:37:38.258986+00:00
-- url     : https://prove2.me/theorems/0188e931-f7a6-43fe-a70b-eaeeda414be9
-- title:
--   Lemma 15.2: the normalized Hard-SVM output (w₀/‖w₀‖, b₀/‖w₀‖) has unit norm and maximizes the margin minᵢ yᵢ(⟨w,xᵢ⟩ + b) over ‖w‖ = 1
-- statement:
--   **Lemma 15.2.** The output of Hard-SVM is a solution of Equation (15.1): $\operatorname{argmax}_{(w,b) : \|w\| = 1} \min_{i \in [m]} y_i(\langle w, x_i\rangle + b)$.
--
--   Formally: for labels in $\{\pm 1\}$ with both labels present, a solution $(w_0, b_0)$ of (15.2) has $w_0 \ne 0$, its normalization has unit norm, and its margin is at least the margin of every halfspace with $\|w\| = 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.1 pp. 204-205, Lemma 15.2 with its proof

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 15.2** (p. 204). The output of Hard-SVM is a solution of Equation (15.1): for a
solution `(w₀, b₀)` of (15.2) on a sample with both labels present, `w₀ ≠ 0`, the normalized
`(ŵ, b̂) = (w₀/‖w₀‖, b₀/‖w₀‖)` has `‖ŵ‖ = 1`, and its margin `minᵢ yᵢ(⟨ŵ, xᵢ⟩ + b̂)` is
maximal among all halfspaces with `‖w‖ = 1`. -/
theorem hard_svm_max_margin {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : ∃ i j, y i = 1 ∧ y j = -1) (w₀ : Vec d) (b₀ : ℝ)
    (h : IsHardSVM x y w₀ b₀) :
    w₀ ≠ 0 ∧ ‖‖w₀‖⁻¹ • w₀‖ = 1 ∧
    ∀ (w : Vec d) (b : ℝ), ‖w‖ = 1 →
      sampleMargin x y w b ≤ sampleMargin x y (‖w₀‖⁻¹ • w₀) (b₀ / ‖w₀‖) := by sorry

end UnderstandingML
