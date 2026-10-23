-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_nonfixed_dimension_two_components
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.nonfixed_dimension_two_components
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:21:23.853985+00:00
-- url     : https://prove2.me/theorems/1a1ae5c2-f329-4446-bef4-c8ea839a2232
-- title:
--   Remark 28
-- statement:
--   In dimension two let $\operatorname{Sp}^*=\{A\in\operatorname{Sp}(2,\mathbb R):\det(A-I)\ne0\}$. Its connected components are exactly
--
--   $$P=\{A\in\operatorname{Sp}(2,\mathbb R):\det(A-I)>0\},\qquad M=\{A\in\operatorname{Sp}(2,\mathbb R):\det(A-I)<0\}.$$
--
--   Both sets are nonempty and connected, they are disjoint, their union is $\operatorname{Sp}^*$, and every connected subset of that union lies in one of them. This expresses both the component count and the component identification without relying on arbitrary component labels.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 32, Remark 28

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Remark 28, PDF p.32: two nonempty connected disjoint exhaustive maximal connected sets. -/
theorem nonfixed_dimension_two_components :
    let P : Set (GroupedRealMatrix 1) := {A | IsSymplectic A ∧ 0 < (A-1).det}
    let M : Set (GroupedRealMatrix 1) := {A | IsSymplectic A ∧ (A-1).det < 0}
    IsConnected P ∧ IsConnected M ∧ Disjoint P M ∧
      {A | IsSymplectic A ∧ (A-1).det ≠ 0} = P ∪ M ∧
      (∀ S : Set (GroupedRealMatrix 1), IsConnected S → S ⊆ P ∪ M → S ⊆ P ∨ S ⊆ M) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
