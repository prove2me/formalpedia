-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_specifiedCircuitOutput
-- name    : QAlgorithms.Papers.Independent.Support50.P24.specifiedCircuitOutput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:00:49.314815+00:00
-- url     : https://prove2.me/theorems/bfb2bef1-ec47-4e5b-ae9c-98ca209d7942
-- title:
--   The specified seven-qubit circuit has the exact output vector
-- statement:
--   For $U\in\mathrm{SU}(2)$ let $f_U=V^{(2)}U_2V^{(1)}U_2$, with the fixed known gates defined by Figs. S2 and S3, including the displayed padding and wire swaps. The physical seven-qubit circuit $f_U^2$ has exactly four forward calls. For every vector $|\phi\rangle\in\mathbb C^2$,
--
--   $$f_U^2\bigl(|\phi\rangle_1\otimes|\psi^-\rangle_{23}\otimes|0^4\rangle_{4\cdots7}\bigr)
--   =-|\psi_U\rangle_{12}\otimes(U^\dagger|\phi\rangle)_3\otimes|0^4\rangle_{4\cdots7},$$
--
--   where $|\psi_U\rangle=(U\otimes I)|\psi^-\rangle$ and $|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$. Physical inputs have $\|\phi\|=1$; the displayed identity extends linearly to all vectors as in (S21). This pins the global minus sign and the complete auxiliary output for the actual specified circuit.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 7, Theorem S1: the full output vector of the specified seven-qubit circuit

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF pp.7-10, Theorem S1 and S21: the specified seven-qubit circuit has the
literal minus sign for SU(2), output on wire 3, catalyst on wires 1,2 and clean zeros.
The identity extends linearly to every vector phi, including zero. -/
theorem specifiedCircuitOutput :
    PhysicalCalls fourCircuit ∧ calls fourCircuit = 4 ∧
    ∀ (U : QubitSU) (phi : Bool → ℂ),
      (evaluateCalls fourCircuit U).mulVec (inputEmbedding.mulVec phi) =
        -((outputEmbedding U * U.valᴴ).mulVec phi) := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
