-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_symplectic_components_and_ambient_loop_contraction
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.symplectic_components_and_ambient_loop_contraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:31:54.496608+00:00
-- url     : https://prove2.me/theorems/109b96d5-58a0-4f3f-9108-18c0a87f3b66
-- title:
--   Theorem 29
-- statement:
--   Let $n\ge1$. The real symplectic group $\operatorname{Sp}(2n,\mathbb R)$ is connected. Its subset $\operatorname{Sp}^*=\{A:\det(A-I)\ne0\}$ has exactly two connected components:
--
--   $$\operatorname{Sp}^+=\{A:\det(A-I)>0\},\qquad
--   \operatorname{Sp}^-=\{A:\det(A-I)<0\}.$$
--
--   Both components are nonempty, connected, disjoint and exhaustive, and every connected subset of $\operatorname{Sp}^*$ lies in one of them. Every continuous loop in either component is homotopic, with its basepoint fixed, to its constant loop in the ambient symplectic group. The homotopy may pass through matrices with eigenvalue $1$. This is the topological input for admissible extensions and their index independence.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 32, Theorem 29

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Theorem 29 ([12]), PDF pp.32–35: connectedness, exactly two nonempty
sign components of Sp*, and based contraction of their loops in ambient Sp.
No requirement keeps the contracting homotopy inside Sp*. -/
theorem symplectic_components_and_ambient_loop_contraction {n : ℕ} (hn : 1 ≤ n) :
    IsConnected {A : GroupedRealMatrix n | IsSymplectic A} ∧
    (let P : Set (GroupedRealMatrix n) := {A | IsSymplectic A ∧ 0 < (A-1).det}
     let M : Set (GroupedRealMatrix n) := {A | IsSymplectic A ∧ (A-1).det < 0}
     IsConnected P ∧ IsConnected M ∧ Disjoint P M ∧
       {A | IsSymplectic A ∧ (A-1).det ≠ 0} = P ∪ M ∧
       (∀ S : Set (GroupedRealMatrix n), IsConnected S → S ⊆ P ∪ M →
         S ⊆ P ∨ S ⊆ M) ∧
       (∀ p : ℝ → GroupedRealMatrix n, IsPath p 1 → p 0 = p 1 →
         ((∀ t ∈ Set.Icc (0 : ℝ) 1, p t ∈ P) ∨
          (∀ t ∈ Set.Icc (0 : ℝ) 1, p t ∈ M)) →
         FixedHomotopic p (fun _ => p 0) 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
