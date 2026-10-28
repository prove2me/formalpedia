-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_euclidean_FCC_failure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.euclidean_FCC_failure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:06:44.211054+00:00
-- url     : https://prove2.me/theorems/f271c164-27fb-41c7-bb8c-c2da3cf99a5f
-- title:
--   §6.4: Euclidean quadrant fails FCC
-- statement:
--   Use \(\mathfrak e(2)=\mathfrak{so}(2)\ltimes\mathbb R^2\), with \([J,P_x]=P_y\), \([J,P_y]=-P_x\). This algebra is solvable, so its true Levi factor is zero. The candidate
--   \[
--   W=\mathbb RJ+\mathbb R_{\ge0}P_x+\mathbb R_{\ge0}P_y
--   \]
--   is a closed convex cone with edge \(\mathbb RJ\) and quadrant translation slice, itself a valid abelian Lie wedge. But \(e^{\pi\operatorname{ad}J}P_x=-P_x\notin W\), so FCC and the Lie-wedge condition fail. The only closed convex cones in the plane invariant under every rotation are zero and the whole plane; any Lie wedge in \(\mathfrak e(2)\) with pointed generating translation slice has zero edge. Separately, the abelian wedge \(\{(s,r):r\ge|s|\}\) has the entire base line but fibers \([|s|,\infty)\), which vary. The complement \(\mathfrak{so}(2)\) is never called a nontrivial Levi factor.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 39, §6.4: Euclidean quadrant fails FCC

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

/-- arXiv:2608.27330v1, PDF pp.39--40, Section 6.4, all counterexample clauses.
The complement/ideal splitting is used only as such. In particular e(2) is solvable. -/
theorem euclidean_FCC_failure :
    ⁅euclideanJ,euclideanPx⁆ = euclideanPy ∧ ⁅euclideanJ,euclideanPy⁆ = -euclideanPx ∧
    LieAlgebra.IsSolvable euclideanAlgebra ∧
    IsClosed euclideanCandidate ∧ IsCone euclideanCandidate ∧
    edge euclideanCandidate = {X | ∃ a : ℝ, X = a • euclideanJ} ∧
    translationSlice euclideanCandidate = quadrant ∧ IsLieWedge quadrant ∧
    expAd (Real.pi • euclideanJ) euclideanPx = -euclideanPx ∧
    -euclideanPx ∉ euclideanCandidate ∧ ¬ IsLieWedge euclideanCandidate ∧
    IsLieWedge absoluteEpigraph ∧ Prod.fst '' absoluteEpigraph = Set.univ ∧
    (∀ a : ℝ, {b : ℝ | (a,b) ∈ absoluteEpigraph} = Set.Ici |a|) ∧
    {b : ℝ | ((0 : ℝ),b) ∈ absoluteEpigraph} ≠ {b : ℝ | ((1 : ℝ),b) ∈ absoluteEpigraph} ∧
    (∀ C : Set (ℝ × ℝ), IsClosed C → IsCone C →
      (∀ t : ℝ, rotatePlane t '' C ⊆ C) → C = {0} ∨ C = Set.univ) ∧
    (∀ W : Set (Matrix (Fin 3) (Fin 3) ℝ), IsLieWedge W →
      W ⊆ (euclideanAlgebra : Set (Matrix (Fin 3) (Fin 3) ℝ)) →
      edge (translationSlice W) = {0} →
      (∀ v : ℝ × ℝ, ∃ x ∈ translationSlice W, ∃ y ∈ translationSlice W, v = x-y) →
      edge W = {0}) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
