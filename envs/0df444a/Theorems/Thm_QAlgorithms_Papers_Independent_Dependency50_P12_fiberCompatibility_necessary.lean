-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_fiberCompatibility_necessary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.fiberCompatibility_necessary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:54:08.967629+00:00
-- url     : https://prove2.me/theorems/e557957d-c1a9-46d4-9dc9-95a60382b89e
-- title:
--   Proposition 4.7: necessity of FCC
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   For every \(X_0\in E(W)\) and \(S\in C\), the transformed base \(S'=e^{\operatorname{ad}\pi_{\mathfrak s}X_0}S\) belongs to \(C\), and
--   \[
--   e^{\operatorname{ad}X_0}(S+F(S))\subseteq S'+F(S').
--   \]
--   This is the full Fiber Compatibility Condition, including its well-defined target base.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 24, Proposition 4.7: necessity of FCC

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

/-- arXiv:2608.27330v1, PDF p.24, Proposition 4.7, Equation (33). -/
theorem fiberCompatibility_necessary (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) : FCC D W := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
