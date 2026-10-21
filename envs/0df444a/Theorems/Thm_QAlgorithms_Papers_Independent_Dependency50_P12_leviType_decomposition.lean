-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_leviType_decomposition
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.leviType_decomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:41:26.393622+00:00
-- url     : https://prove2.me/theorems/90159a8d-e0e9-4e51-9263-de508624d707
-- title:
--   Theorem 4.9: Levi-Type Decomposition Theorem (seed abstract result)
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   The decomposition, reconstruction, and correspondence assertions all hold. The radical slice is a Lie wedge with edge \(E(W)\cap\mathfrak r\); the possibly nonclosed cone \(C\) is invariant under the closed Lie subalgebra \(E_{\rm quot}\); the fibers are nonempty closed convex sets, \(F(0)=W_{\mathfrak r}\), subadditive, nonnegatively homogeneous with equality at strictly positive scales, and have closed graph in the full product. Edge action satisfies
--   \[
--   e^{\operatorname{ad}X_0}(S+F(S))
--    \subseteq e^{\operatorname{ad}\pi_{\mathfrak s}X_0}S+
--    F(e^{\operatorname{ad}\pi_{\mathfrak s}X_0}S).
--   \]
--   Conversely, a convex cone containing zero and fibers satisfying D1--D4 (nonempty closed convex fibers, subadditivity, nonnegative homogeneity, and full-product closed graph), D5 (base invariance under the edge computed from opposite fibers), and D6 (the displayed compatibility) reconstruct the unique Lie wedge with those data:
--   \[
--   W=\bigcup_{S\in C}(S+F(S)).
--   \]
--   Both constructions are mutually inverse, with equality of fibers over their prescribed base. This is an exact coordinate description relative to the chosen splitting.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 26, Theorem 4.9: Levi-Type Decomposition Theorem (seed abstract result)

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

/-- arXiv:2608.27330v1, PDF p.26, Theorem 4.9, all three parts.
All components are computed from W; reconstruction and both inverse identities
are conclusions. Fibers of abstract data are identified only over their base. -/
theorem leviType_decomposition (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    (IsLieWedge (radicalSlice D W) ∧
      edge (radicalSlice D W) = {R : D.r | (R : A) ∈ edge W} ∧
      QuotientProperties D W ∧ FiberProperties D W ∧ FCC D W) ∧
    (∀ (C : Set D.s) (F : D.s → Set D.r), AdmissibleLeviFibers D C F →
      ReconstructionResult D C F) ∧
    (AdmissibleLeviFibers D (quotientCone D W) (fiber D W) ∧
      reconstructLeviFibers D (quotientCone D W) (fiber D W) = W) ∧
    (∀ (C : Set D.s) (F : D.s → Set D.r), AdmissibleLeviFibers D C F →
      quotientCone D (reconstructLeviFibers D C F) = C ∧
      ∀ S ∈ C, fiber D (reconstructLeviFibers D C F) S = F S) := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
