-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_closedSubspace_isKSpace
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.closedSubspace_isKSpace
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:27:41.588843+00:00
-- url     : https://prove2.me/theorems/748a6e22-7ccd-406b-b7f9-4b95248bbedf
-- title:
--   Theorem B.9
-- statement:
--   Let $X$ be a compactly Hausdorff generated space and $A\subseteq X$ a closed subset with the induced topology. Then
--
--   $$A\text{ is compactly Hausdorff generated}.$$
--
--   The ambient space and the closed subspace need not satisfy a Hausdorff axiom. The empty closed subset is allowed.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, Theorem B.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Theorem B.9, PDF pp. 36–37: every closed subspace of a k-space is a
k-space. No Hausdorff axiom is imposed on the ambient space. -/
theorem closedSubspace_isKSpace
    (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    (A : Set X) (hA : IsClosed A) : UCompactlyGeneratedSpace.{u} A := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
