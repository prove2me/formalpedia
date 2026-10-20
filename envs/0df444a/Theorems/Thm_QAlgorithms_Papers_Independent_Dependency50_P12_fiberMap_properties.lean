-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_fiberMap_properties
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.fiberMap_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:53:08.993419+00:00
-- url     : https://prove2.me/theorems/2cbf4086-4b38-47bb-b9f6-6838444f6653
-- title:
--   Lemma 4.6: five properties of the fiber map
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   Every fiber over \(C\) is nonempty, closed, and convex. The remaining identities and inclusions are
--   \[
--   F(0)=W_{\mathfrak r},\quad
--   F(S)+F(T)\subseteq F(S+T),\quad
--   aF(S)\subseteq F(aS)\quad(a\ge0),
--   \]
--   with equality in the scaling formula for \(a>0\). The graph \(\{(S,R):S\in C,\ R\in F(S)\}\) is closed in all of \(\mathfrak s\times\mathfrak r\). These properties describe the actual fibers rather than auxiliary sets assumed to satisfy them.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 23, Lemma 4.6: five properties of the fiber map

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

/-- arXiv:2608.27330v1, PDF p.23, Lemma 4.6, all five properties. -/
theorem fiberMap_properties (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) : FiberProperties D W := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
