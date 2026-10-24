-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_catalyticThreeCalls
-- name    : QAlgorithms.Papers.Independent.Support50.P24.catalyticThreeCalls
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:56:37.542986+00:00
-- url     : https://prove2.me/theorems/00aceb16-3715-4e02-aca1-d61a7b72c3b5
-- title:
--   Exact three-call inversion with a returned catalyst
-- statement:
--   Let $U\in\mathrm{SU}(2)$ be unknown and let $|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$. Supply the particular catalyst $|\psi_U\rangle=(U\otimes I)|\psi^-\rangle$ for this same $U$. The fixed circuit obtained from Fig. 1 by deleting its first oracle call uses three forward calls and satisfies
--
--   $$\rho_1\otimes|\psi_U\rangle\langle\psi_U|_{23}\otimes|0^4\rangle\langle0^4|_{4\cdots7}
--   \longmapsto |\psi_U\rangle\langle\psi_U|_{12}\otimes(U^\dagger\rho U)_3\otimes|0^4\rangle\langle0^4|_{4\cdots7}.$$
--
--   The equality includes reference-entangled inputs. It returns the catalyst for reuse with the same unknown operation; it does not assert three-call inversion without advice. The density-matrix formula includes the physical wire relabelling and removes the circuit's global minus sign.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 2, Unnumbered main result, Eq.(1): exact catalytic inversion with three calls

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF p.2, Eq.(1): three forward calls with the specified same-U catalyst return
that catalyst while inverting the input. Full output channel equality suppresses global phase. -/
theorem catalyticThreeCalls :
    PhysicalCalls catalyticCircuit ∧ calls catalyticCircuit = 3 ∧
    ∀ (U : QubitSU) (A : Matrix Bool Bool ℂ),
      conjSuperop (evaluateCalls catalyticCircuit U * catalyticInput U) A =
        conjSuperop (outputEmbedding U * U.valᴴ) A := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
