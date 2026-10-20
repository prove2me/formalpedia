-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_quotient_closedness_criteria
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.quotient_closedness_criteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:57:35.79941+00:00
-- url     : https://prove2.me/theorems/27405fb9-f5d5-4de6-aa4c-8a86ddd6e58b
-- title:
--   Remark 4.5: projection may fail closedness; three sufficient conditions
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   The closed convex cone
--   \[
--   K=\{(x,y,z):x\ge0,\ z\ge0,\ y^2\le xz\}
--   \]
--   projects under \((x,y,z)\mapsto(y,z)\) to \(\{(y,z):z>0\}\cup\{(0,0)\}\), which is not closed. Independently, each of the following is sufficient for \(C\) to be closed: \(W\cap\mathfrak r\subseteq E(W)\); polyhedrality of \(W\), in which case its image is also polyhedral; or \(E_{\rm quot}=\mathfrak s\), in which case \(C=\mathfrak s\). The projection example makes no claim of physical realization.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 22, Remark 4.5: projection may fail closedness; three sufficient conditions

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

section ProjectionClosedness

/-- arXiv:2608.27330v1, PDF p.22, Remark 4.5.
The three sufficient conditions are separate implications. The concrete example
is about linear cone projection, without asserting a physical realization. -/
theorem quotient_closedness_criteria
    {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]
    (D : LeviSplitting A) (W : Set A) (hW : IsLieWedge W) :
    (IsClosed projectionExample ∧ IsCone projectionExample ∧
      yzProjection '' projectionExample = {p : ℝ × ℝ | 0 < p.2 ∨ p = 0} ∧
      ¬ IsClosed (yzProjection '' projectionExample)) ∧
    ((∀ R ∈ radicalSlice D W, (R : A) ∈ edge W) → IsClosed (quotientCone D W)) ∧
    (PolyhedralCone W → PolyhedralCone (quotientCone D W) ∧ IsClosed (quotientCone D W)) ∧
    (projectedEdge D W = Set.univ →
      quotientCone D W = Set.univ ∧ IsClosed (quotientCone D W)) := by sorry

end ProjectionClosedness

end QAlgorithms.Papers.Independent.Dependency50.P12

end
