-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_prior_entanglement_preparation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.prior_entanglement_preparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:05:07.815529+00:00
-- url     : https://prove2.me/theorems/978bce59-d3aa-4743-a914-dd999652c821
-- title:
--   Free input-independent preparation of prior entanglement
-- statement:
--   Let $\psi$ be any unit vector on $N$ qubits, and specify which qubits Alice and Bob should own. There is an input-independent unitary $U$ and a legal one-message preparation phase such that
--   $$
--   U\lvert0^N\rangle=\lvert\psi\rangle.
--   $$
--
--   Alice initially owns all $N$ blank qubits and applies $U$ locally. The constructed preparation round transfers exactly the wires assigned to Bob, leaving precisely the prescribed final ownership and shared state. All preparation communication is uncharged and precedes the inputs and the counted protocol.
--
--   This realizes arbitrary finite input-independent prior entanglement without granting input-dependent assistance. The zero-qubit case is included, with an empty transfer and a unit complex phase.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 7, Paragraph preceding Definition 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Unnumbered equivalence preceding Definition 6, PDF p.7: every finite normalized prior
entangled state is prepared with input-independent local work and uncharged communication.
The constructed round transfers actual owned qubits and realizes exactly the requested ownership. -/
theorem prior_entanglement_preparation (N : ℕ) (own : Fin N → Party)
    (psi : EuclideanSpace ℂ (Qubits N)) (hpsi : ‖psi‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Qubits N) ℂ,
      act (U : Matrix (Qubits N) (Qubits N) ℂ) (ket (fun _ => false)) = psi ∧
      roundsLegal (fun _ => .alice) [preparationRound own U] ∧
      (preparationRound own U).update (fun _ => .alice) = own := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
