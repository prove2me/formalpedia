-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_radicalSlice_isLieWedge
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.radicalSlice_isLieWedge
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:51:31.091931+00:00
-- url     : https://prove2.me/theorems/e44bbab6-a15a-4bd0-80ce-2d693f49d03d
-- title:
--   Lemma 4.2: radical slice is a Lie wedge
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   The radical slice is a Lie wedge in the radical Lie algebra, and
--   \[
--   E(W_{\mathfrak r})=E(W)\cap\mathfrak r.
--   \]
--   This identifies the reversible radical directions without requiring either factor to be nonzero.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 21, Lemma 4.2: radical slice is a Lie wedge

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

/-- arXiv:2608.27330v1, PDF p.21, Lemma 4.2. -/
theorem radicalSlice_isLieWedge (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    IsLieWedge (radicalSlice D W) ∧
    edge (radicalSlice D W) = {R : D.r | (R : A) ∈ edge W} := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
