-- Prove2me | Theorems.Thm_ShiShallow_cnotState_eq_cnotMatrix_mulVec
-- name    : ShiShallow.cnotState_eq_cnotMatrix_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T18:22:58.119264+00:00
-- url     : https://prove2.me/theorems/de1180c1-44d7-4f19-8b37-c49a02e403a5
-- title:
--   CNOT: state-function semantics equals the matrix-vector action, for distinct wires
-- statement:
--   This closes the other gate-level half of the gap between the development's two independent semantics. CNOT with control i and target j sends a state to the function whose value at a string is the old amplitude at the string with position j flipped by the value at position i. The matrix semantics turns the same gate into a square matrix with entry one exactly when a guard relating row and column strings holds. Here the two are shown to agree.
--
--   MECHANISM: a SINGLE-point collapse, simpler than the one-qubit case. The guard pins the column string completely -- it must agree with the row away from the two touched positions, agree at the control, and equal the exclusive-or of target and control at the target. Those three conditions determine the column uniquely, and the survivor is exactly the updated string appearing on the state-function side. So each row has exactly ONE nonzero entry, equal to one, and the sum reduces to a single term. Contrast the one-qubit gate, where two entries per row survive.
--
--   THE DISTINCTNESS HYPOTHESIS IS ESSENTIAL, not decoration. The matrix definition carries no such hypothesis, and when control and target coincide the guard DEGENERATES: it demands the column agree with the row at that position and that the same bit equal the exclusive-or of itself with itself, namely false. Only rows with a false bit there have any nonzero entry, so the matrix is rank-deficient and is NOT the CNOT matrix. The identity is therefore genuinely FALSE without distinctness, which is used in exactly one place -- evaluating the updated string at the control position -- precisely where the degenerate case breaks.
--
--   HONEST LIMITATIONS. This is ONE gate, not a circuit: the layer and circuit levels -- where the matrix product runs opposite to application order -- remain separate. Nothing is claimed about layer well-formedness. No universality claim for the H, S, T, X, CNOT gate set. Unitarity is neither assumed nor proved: although CNOT on distinct wires happens to be a permutation matrix and hence unitary, that is NOT what is shown, and the development still contains no unitarity lemma for any gate matrix.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open Matrix

theorem cnotState_eq_cnotMatrix_mulVec {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotState i j hij ψ = cnotMatrix i j *ᵥ ψ := by
  sorry

end ShiShallow
