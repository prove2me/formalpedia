-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_affine_invariantCone_iff_zero
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.affine_invariantCone_iff_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:03:43.126828+00:00
-- url     : https://prove2.me/theorems/f1e16736-c601-469f-aafd-70d4828d9f6d
-- title:
--   Proposition 6.1: affine algebra has no pointed generating invariant cone
-- statement:
--   For a finite-dimensional real vector space \(V\), a full-adjoint-invariant closed convex cone in \(\mathfrak{aff}(V)=\mathfrak{gl}(V)\ltimes V\) is pointed when its edge is zero and generating when its difference with itself is the entire algebra. Then
--   \[
--   \mathfrak{aff}(V)\text{ admits a pointed generating invariant cone}
--    \iff V=\{0\}.
--   \]
--   The coordinate statement uses \(V=\mathbb R^n\), covering every finite-dimensional \(V\), and retains \(n=0\).
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 37, Proposition 6.1: affine algebra has no pointed generating invariant cone

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

/-- arXiv:2608.27330v1, PDF p.37, Proposition 6.1.
Coordinates cover every finite-dimensional real V. Generating means W-W=aff(V),
and the zero-dimensional boundary is retained in the equivalence. -/
theorem affine_invariantCone_iff_zero (n : ℕ) :
    (∃ W : Set (affineAlgebra n), IsClosed W ∧ IsCone W ∧ edge W = {0} ∧
      (∀ X : affineAlgebra n, ∃ Y ∈ W, ∃ Z ∈ W, X = Y - Z) ∧
      (∀ X : affineAlgebra n, expAd X '' W ⊆ W)) ↔ n = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
