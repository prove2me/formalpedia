-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_edge_fiber_formula
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.edge_fiber_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:55:39.620552+00:00
-- url     : https://prove2.me/theorems/0cd23c8e-6ac2-4d93-a57b-9e270e995f8b
-- title:
--   Corollary 4.11: exact edge fiber formula
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   For \(S\in\mathfrak s\) and \(R\in\mathfrak r\),
--   \[
--   S+R\in E(W)\iff
--    S\in C\cap(-C),\quad R\in F(S),\quad -R\in F(-S).
--   \]
--   Consequently \(E(W)\) is the union of these opposite-fiber intersections translated by their base points. The base lineality alone does not determine the wedge edge.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 26, Corollary 4.11: exact edge fiber formula

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

/-- arXiv:2608.27330v1, PDF p.26, Corollary 4.11, including Equation (42). -/
theorem edge_fiber_formula (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    (∀ (S : D.s) (R : D.r), (S : A) + (R : A) ∈ edge W ↔
      S ∈ edge (quotientCone D W) ∧ R ∈ fiber D W S ∧ -R ∈ fiber D W (-S)) ∧
    edge W = candidateEdge D (quotientCone D W) (fiber D W) := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
