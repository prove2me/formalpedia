-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_reconstruct_admissible
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.reconstruct_admissible
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:54:53.628273+00:00
-- url     : https://prove2.me/theorems/30a39d89-5e35-4340-a627-ec1d7550a6b8
-- title:
--   Proposition 4.8: reconstruction from actual D1–D6 data
-- statement:
--   Fix a finite-dimensional real Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\). Let \(C\subseteq\mathfrak s\) be a convex cone containing zero, not assumed closed, and prescribe \(F(S)\subseteq\mathfrak r\) for \(S\in C\). Assume D1--D4: nonempty closed convex fibers, subadditivity, nonnegative homogeneity, and a graph closed in the full product. Compute
--   \[
--   \mathcal E=\bigcup_{S\in C\cap(-C)}
--    \bigl(S+(F(S)\cap(-F(-S)))\bigr).
--   \]
--   Assume D5, that \(C\) is invariant under \(e^{\operatorname{ad}\pi_{\mathfrak s}X_0}\) for \(X_0\in\mathcal E\), and D6, that \(e^{\operatorname{ad}X_0}(S+F(S))\subseteq S'+F(S')\), where \(S'=e^{\operatorname{ad}\pi_{\mathfrak s}X_0}S\). Then
--   \[
--   W=\bigcup_{S\in C}(S+F(S))
--   \]
--   is a Lie wedge, \(W\cap\mathfrak r=F(0)\), \(\pi_{\mathfrak s}(W)=C\), \(E(W)=\mathcal E\), and its fibers are exactly the prescribed fibers. It is the unique subset with that projection and those fibers. No wedge or pre-existing edge is input.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 24, Proposition 4.8: reconstruction from actual D1–D6 data

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

/-- arXiv:2608.27330v1, PDF pp.24--25, Proposition 4.8.
There is no presupposed wedge among the hypotheses. -/
theorem reconstruct_admissible (D : LeviSplitting A) (C : Set D.s)
    (F : D.s → Set D.r) (h : AdmissibleLeviFibers D C F) :
    ReconstructionResult D C F := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
