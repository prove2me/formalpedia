-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_deterministicExactFourCalls
-- name    : QAlgorithms.Papers.Independent.Support50.P24.deterministicExactFourCalls
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:55:46.651004+00:00
-- url     : https://prove2.me/theorems/0a56905a-62ac-4339-8dc3-6a4891feeb60
-- title:
--   Theorem 1: deterministic exact four-call inversion
-- statement:
--   There is a fixed seven-qubit quantum circuit with exactly four forward calls to an unknown $U\in\mathrm{SU}(2)$, using the same $U$ at every call. Its inserted gates, singlet on input wires 2 and 3, and four zero ancillas are independent of $U$ and the input. After discarding every output wire except wire 3, its channel is
--
--   $$\rho\longmapsto U^\dagger\rho U.$$
--
--   This equality holds on every input density matrix and after tensoring with the identity on any reference system. The auxiliary output may depend on $U$. The result establishes deterministic exact inversion without a supplied catalyst.
--
--   **Formalization Note** Equality is stated on all matrices; for these linear channels this is equivalent to channel equality on states, including entangled inputs.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 2, Theorem 1: deterministic exact four-call qubit-unitary inversion

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF pp.1-2, Theorem 1: a fixed circuit uses exactly four forward calls and
implements the inverse channel on all inputs, including reference-entangled inputs. -/
theorem deterministicExactFourCalls :
    ∃ gates : List CallGate, PhysicalCalls gates ∧ calls gates = 4 ∧ ExactInverter gates := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
