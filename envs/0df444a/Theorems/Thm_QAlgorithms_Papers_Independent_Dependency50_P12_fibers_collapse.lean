-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_fibers_collapse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.fibers_collapse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:56:08.852743+00:00
-- url     : https://prove2.me/theorems/0f3bbc78-e12b-4b28-ab44-caaaa0bc7868
-- title:
--   Proposition 4.12: sufficient collapse criterion
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   If every base point, embedded in \(\mathfrak g\), belongs to \(E(W)\), then
--   \[
--   F(S)=W_{\mathfrak r}\quad(S\in C),\qquad W=C+W_{\mathfrak r}.
--   \]
--   When both factors are nonzero, each has dimension strictly smaller than \(\dim\mathfrak g\). This is a sufficient collapse criterion and does not assert a converse.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 27, Proposition 4.12: sufficient collapse criterion

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

/-- arXiv:2608.27330v1, PDF p.27, Proposition 4.12.
The two strict dimension reductions are conditional on BOTH factors being nonzero. -/
theorem fibers_collapse (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W)
    (hC : ∀ S ∈ quotientCone D W, (S : A) ∈ edge W) :
    (∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W) ∧
    W = {x | ∃ S ∈ quotientCone D W, ∃ R ∈ radicalSlice D W,
      x = (S : A) + (R : A)} ∧
    (D.s ≠ ⊥ → D.r ≠ ⊥ →
      Module.finrank ℝ D.s < Module.finrank ℝ A ∧
      Module.finrank ℝ D.r < Module.finrank ℝ A) := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
