-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_quotientCone_structure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.quotientCone_structure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:52:30.926838+00:00
-- url     : https://prove2.me/theorems/f0af18d4-3b1f-4c05-b7c7-d3d6fc25e427
-- title:
--   Lemma 4.3: quotient cone and projected edge
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   The set \(C\) is a convex cone containing zero, and \(E_{\rm quot}\) is a closed Lie subalgebra of \(\mathfrak s\). Moreover,
--   \[
--   e^{\operatorname{ad}S_0}(C)\subseteq C
--   \qquad(S_0\in E_{\rm quot}).
--   \]
--   Closedness of \(C\) is not asserted. The acting algebra is the projected edge, which need not equal \(C\cap(-C)\).
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 21, Lemma 4.3: quotient cone and projected edge

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

/-- arXiv:2608.27330v1, PDF pp.21--22, Lemma 4.3. -/
theorem quotientCone_structure (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) : QuotientProperties D W := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
