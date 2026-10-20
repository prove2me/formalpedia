-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_twoQubit_controlAverage
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.twoQubit_controlAverage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:03:09.174853+00:00
-- url     : https://prove2.me/theorems/b0217c8d-7a39-4e0b-9469-30fdcb2f2c28
-- title:
--   §5.2: control averages lie in a single radical ray
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For the same independently controlled two-qubit system, average control conjugation using normalized Haar measure on \(SU(2)_A\). Both continuous finite-dimensional dissipator orbits are integrable. The normalized averages coincide and are nonzero:
--   \[
--   \overline D_0=\int\operatorname{Ad}_U D_{J_0}\,dU
--   =\int\operatorname{Ad}_U D_{J_1}\,dU=\overline D_1.
--   \]
--   They belong to the radical and the local wedge and are fixed by the control edge. Positive rates only rescale this common average: the averages of \(\gamma_iD_{J_i}\) are \(\gamma_i\overline D_0\), without equality between unequal rate-weighted averages. Every control-fixed algebra element belongs to the radical, reflecting the absence of fixed vectors in the three-adjoint-copy quotient. The average generates a contained radical ray, without identifying the entire radical wedge with that ray.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 36, §5.2: control averages lie in a single radical ray

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

section ControlAverages

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.controlGroupMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.controlGroupBorelSpace

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.superContinuousENorm

/-- arXiv:2608.27330v1, PDF p.36, Section 5.2, Equation (61).
The measure is SU(2) Haar pushed into U(2): total mass one, supported on det=1,
and invariant under left multiplication by every determinant-one unitary. -/
theorem twoQubit_controlAverage
    (mu : MeasureTheory.Measure (Matrix.unitaryGroup (Fin 2) ℂ))
    [MeasureTheory.IsProbabilityMeasure mu]
    (hsupport : mu {U | (U : P59.Operator 2).det ≠ 1} = 0)
    (hhaar : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, (V : P59.Operator 2).det = 1 →
      MeasureTheory.Measure.map (fun U => V*U) mu = mu) :
    MeasureTheory.Integrable (fun U => controlConjugation U (dissipatorMap modulatedJ0)) mu ∧
    MeasureTheory.Integrable (fun U => controlConjugation U (dissipatorMap modulatedJ1)) mu ∧
    controlAverage mu (dissipatorMap modulatedJ0) = controlAverage mu (dissipatorMap modulatedJ1) ∧
    controlAverage mu (dissipatorMap modulatedJ0) ≠ 0 ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      controlAverage mu (a • dissipatorMap modulatedJ0) =
        a • controlAverage mu (dissipatorMap modulatedJ0) ∧
      controlAverage mu (b • dissipatorMap modulatedJ1) =
        b • controlAverage mu (dissipatorMap modulatedJ0)) ∧
    (∀ i : Fin 2, ∃ R : LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG,
      (R : Super 4) = controlAverage mu (dissipatorMap (if i = 0 then modulatedJ0 else modulatedJ1)) ∧
      R ∈ LieAlgebra.radical ℝ (LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG) ∧
      (R : Super 4) ∈ minimalWedge twoQubitG) ∧
    (∀ X ∈ twoQubitControl,
      expAd X (controlAverage mu (dissipatorMap modulatedJ0)) =
        controlAverage mu (dissipatorMap modulatedJ0)) ∧
    (∀ L : LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG,
      (∀ X ∈ twoQubitControl, ⁅X,(L : Super 4)⁆ = 0) →
      L ∈ LieAlgebra.radical ℝ (LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG)) := by sorry

end ControlAverages

end QAlgorithms.Papers.Independent.Dependency50.P12

end
