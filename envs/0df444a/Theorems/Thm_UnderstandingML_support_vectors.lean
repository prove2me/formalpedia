-- Prove2me | Theorems.Thm_UnderstandingML_support_vectors
-- name    : UnderstandingML.support_vectors
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:40:34.055336+00:00
-- url     : https://prove2.me/theorems/57f8f5bf-41de-4df1-8eef-3175f0417f89
-- title:
--   Theorem 15.8: the homogenous Hard-SVM solution w₀ is a linear combination of the support vectors {xᵢ : |⟨w₀,xᵢ⟩| = 1}
-- statement:
--   **Theorem 15.8.** Let $w_0$ be as defined in Equation (15.3) and let $I = \{i : |\langle w_0, x_i\rangle| = 1\}$. Then there exist coefficients $\alpha_1, \dots, \alpha_m$ such that $w_0 = \sum_{i \in I}\alpha_i x_i$. The examples $\{x_i : i \in I\}$ are called support vectors.
--
--   Formally: labels in $\{\pm1\}$; the coefficients vanish outside $I$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.3 p. 210, Theorem 15.8 (from Lemma 15.9)

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 15.8** (p. 210). Let `w₀` be the solution of the homogenous Hard-SVM problem (15.3)
and let `I = {i : |⟨w₀, xᵢ⟩| = 1}`. Then there exist coefficients `α₁, …, α_m` such that
`w₀ = ∑_{i ∈ I} αᵢ xᵢ`; the examples `{xᵢ : i ∈ I}` are the support vectors. Labels in `{±1}`. -/
theorem support_vectors {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (w₀ : Vec d) (h : IsHomHardSVM x y w₀) :
    ∃ α : Fin m → ℝ, (∀ i, |⟪w₀, x i⟫_ℝ| ≠ 1 → α i = 0) ∧ w₀ = ∑ i, α i • x i := by sorry

end UnderstandingML
