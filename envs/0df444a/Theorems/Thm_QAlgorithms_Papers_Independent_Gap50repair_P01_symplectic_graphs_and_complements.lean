-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_symplectic_graphs_and_complements
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.symplectic_graphs_and_complements
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:29:46.421712+00:00
-- url     : https://prove2.me/theorems/c31ea873-5221-4ea1-9237-2073cb55fe05
-- title:
--   Unnumbered: symplectic graphs and complements
-- statement:
--   Equip $\mathbb R^{2n}\times\mathbb R^{2n}$ with $-\Omega_0\oplus\Omega_0$. For every real linear map $A$ its graph has dimension $2n$, and
--
--   $$\operatorname{Gr}A\text{ is Lagrangian}\quad\Longleftrightarrow\quad A\text{ is symplectic}.$$
--
--   In particular the diagonal $\Delta=\operatorname{Gr}I$ is Lagrangian. If $A$ is symplectic, $\operatorname{Gr}(-A)$ is Lagrangian and complementary to $\operatorname{Gr}A$. For arbitrary linear maps $A,B$, their graphs are complementary if and only if $A-B$ is invertible. These assertions supply all graph and complement clauses introducing the generalized index.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 47, Unnumbered: symplectic graphs and complements

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Unnumbered graph/complement results, PDF p.47, for arbitrary linear maps. -/
theorem symplectic_graphs_and_complements {n : ℕ} :
    (∀ A : GroupedRealMatrix n, Module.finrank ℝ (graphSpace A) = 2*n ∧
      (IsGraphLagrangian (graphSpace A) ↔ IsSymplectic A)) ∧
    IsGraphLagrangian (graphSpace (1 : GroupedRealMatrix n)) ∧
    (∀ A : GroupedRealMatrix n, IsSymplectic A → IsGraphLagrangian (graphSpace (-A)) ∧
      IsCompl (graphSpace A) (graphSpace (-A))) ∧
    (∀ A B : GroupedRealMatrix n, IsCompl (graphSpace A) (graphSpace B) ↔ (A-B).det ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
