-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_gaussian_bidirectional_constant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.gaussian_bidirectional_constant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:06:07.440171+00:00
-- url     : https://prove2.me/theorems/dd11c2d7-841c-49f3-b901-e504f4b827b9
-- title:
--   §6.3: bidirectional Gaussian extension has constant fibers
-- statement:
--   In the finite Gaussian moment representation, take the two Hamiltonian drifts
--   \[
--   S_1=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad
--   S_2=\begin{pmatrix}0&1\\1&0\end{pmatrix}
--   \]
--   with both signs available, together with a one-sided damping moment pair of rate \(\gamma>0\). The generated algebra has dimension seven. A Levi complement is the actual zero-diffusion trace-zero \(2\times2\) drift algebra, isomorphic to \(\mathfrak{sl}(2,\mathbb R)\), and has dimension three. Its entire quotient lies in the edge, so
--   \[
--   C_{\rm quot}=\mathfrak s,\qquad F(S)=W_{\mathfrak r}\quad(S\in\mathfrak s).
--   \]
--   The positive damping assumption prevents the dimension from degenerating.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 39, §6.3: bidirectional Gaussian extension has constant fibers

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

/-- arXiv:2608.27330v1, PDF p.39, Section 6.3, symmetric extension.
The displayed Levi factor is the actual embedded trace-zero 2 by 2 algebra,
isomorphic to sl(2,R); it is not an arbitrary algebra with supplied conclusions. -/
theorem gaussian_bidirectional_constant (gamma : ℝ) (hg : 0 < gamma) :
    let g := LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianExtensionG gamma)
    let W : Set g := {X | (X : Matrix (Fin 6) (Fin 6) ℝ) ∈ minimalWedge (gaussianExtensionG gamma)}
    Module.finrank ℝ g = 7 ∧
    ∃ D : LeviSplitting g,
      (D.s : Set g) = {X : g | ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
        A.trace = 0 ∧ (X : Matrix (Fin 6) (Fin 6) ℝ) = momentMap A 0} ∧
      Module.finrank ℝ D.s = 3 ∧ quotientCone D W = Set.univ ∧
      (∀ S : D.s, (S : g) ∈ edge W) ∧
      (∀ S : D.s, fiber D W S = radicalSlice D W) ∧
      IsLieWedge W := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
