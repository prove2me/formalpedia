-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_ancilla_phase_cloner
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.ancilla_phase_cloner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:12:03.055683+00:00
-- url     : https://prove2.me/theorems/8dea51b7-ae64-42e5-8119-6812d7bd6ba3
-- title:
--   §II.D.3 Eqs.(41)–(42): ancilla version with the same equatorial fidelities
-- statement:
--   For $0\le\theta\le\pi/2$, the four columns 000,100,011,111 in (41) admit a common three-qubit unitary extension. On input $\psi_A\Phi^+_{BM}$ it agrees with (42), with the identity on the machine outside the entire Pauli sum. For every equatorial input,
--
--   $$
--   F_A=\frac{1+\cos\theta}{2},\qquad F_B=\frac{1+\sin\theta}{2}.
--   $$
--
--   Thus this ancilla realization has the same equatorial cloning fidelities as the economical realization, although the retained machine can carry additional eavesdropping information.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 12, §II.D.3 Eqs.(41)–(42): ancilla version with the same equatorial fidelities

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.D.3, PDF p.12 Eqs.(41)–(42): four specified columns admit a unitary
extension; the ancilla construction has the same equatorial fidelities. -/
theorem ancilla_phase_cloner (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ Real.pi / 2) :
    ∃ U : Matrix.unitaryGroup (Triple 2) ℂ,
      WithLp.toLp 2 ((U : Matrix (Triple 2) (Triple 2) ℂ).mulVec (ket (0, (0, 0)))) = ket (0, (0, 0)) ∧
      WithLp.toLp 2 ((U : Matrix (Triple 2) (Triple 2) ℂ).mulVec (ket (1, (1, 1)))) = ket (1, (1, 1)) ∧
      WithLp.toLp 2 ((U : Matrix (Triple 2) (Triple 2) ℂ).mulVec (ket (1, (0, 0)))) =
        (Real.cos theta : ℂ) • ket (1, (0, 0)) + (Real.sin theta : ℂ) • ket (0, (1, 0)) ∧
      WithLp.toLp 2 ((U : Matrix (Triple 2) (Triple 2) ℂ).mulVec (ket (0, (1, 1)))) =
        (Real.cos theta : ℂ) • ket (0, (1, 1)) + (Real.sin theta : ℂ) • ket (1, (0, 1)) ∧
      (∀ psi : EuclideanSpace ℂ (Fin 2),
        WithLp.toLp 2 ((U : Matrix (Triple 2) (Triple 2) ℂ).mulVec (tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 2)))) = phaseOutput theta psi) ∧
      (∀ psi : EuclideanSpace ℂ (Fin 2), WithLp.toLp 2 ((phaseCerf theta).mulVec (tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 2)))) = phaseOutput theta psi) ∧
      (∀ a : ℝ, pureFidelity (equator a) (cloneMarginalA (phaseOutput theta (equator a))) = (1 + Real.cos theta) / 2 ∧
        pureFidelity (equator a) (cloneMarginalB (phaseOutput theta (equator a))) = (1 + Real.sin theta) / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
