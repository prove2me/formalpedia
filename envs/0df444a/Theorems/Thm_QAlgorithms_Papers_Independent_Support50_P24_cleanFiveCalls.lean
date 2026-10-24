-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_cleanFiveCalls
-- name    : QAlgorithms.Papers.Independent.Support50.P24.cleanFiveCalls
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:59:04.727984+00:00
-- url     : https://prove2.me/theorems/b6a8de74-356e-4c4e-95ef-8bce3b43d1cc
-- title:
--   Clean exact inversion with five forward calls
-- statement:
--   Let $U\in\mathrm{SU}(2)$ be unknown. Append one forward call to printed wire 2 of the four-call circuit of Fig. 1. This fixed circuit uses exactly five forward calls. For every input density matrix $\rho$ it produces
--
--   $$|\psi^-\rangle\langle\psi^-|_{12}\otimes(U^\dagger\rho U)_3\otimes|0^4\rangle\langle0^4|_{4\cdots7},$$
--
--   from $\rho_1\otimes|\psi^-\rangle\langle\psi^-|_{23}\otimes|0^4\rangle\langle0^4|_{4\cdots7}$. The equality remains valid with a reference system. All final auxiliary registers are independent of $U$, which is the source's meaning of clean. The auxiliary wire layout may differ from the initial layout. This gives clean deterministic exact inversion; no thermodynamic cost estimate is asserted.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 4, Unnumbered main result: clean exact inversion with five calls

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF p.4: five forward calls achieve inversion with a final auxiliary state
independent of U, here singlet on wires 1,2 and four zero qubits on wires 4,...,7. -/
theorem cleanFiveCalls :
    PhysicalCalls cleanCircuit ∧ calls cleanCircuit = 5 ∧
    ∀ (U : QubitSU) (A : Matrix Bool Bool ℂ),
      conjSuperop (evaluateCalls cleanCircuit U * inputEmbedding) A =
        conjSuperop (swappedEmbedding * U.valᴴ) A := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
