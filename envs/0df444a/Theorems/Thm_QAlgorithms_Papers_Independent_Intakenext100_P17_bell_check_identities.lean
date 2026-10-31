-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P17_bell_check_identities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P17.bell_check_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:17:57.01103+00:00
-- url     : https://prove2.me/theorems/2d19af35-e0ec-43a1-a053-21e53fc76753
-- title:
--   Bell projectors reproduce the two check-error effects
-- statement:
--   Let $|\Phi^\pm\rangle=(|00\rangle\pm|11\rangle)/\sqrt2$ and $|\Psi^\pm\rangle=(|01\rangle\pm|10\rangle)/\sqrt2$, and let $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$. On the two-qubit space,
--
--   $$
--   |\Psi^+\rangle\langle\Psi^+|+|\Psi^-\rangle\langle\Psi^-|=|01\rangle\langle01|+|10\rangle\langle10|,
--   $$
--   $$
--   |\Phi^-\rangle\langle\Phi^-|+|\Psi^-\rangle\langle\Psi^-|=|+-\rangle\langle+-|+|-+\rangle\langle-+|.
--   $$
--
--   Thus computational-basis disagreement and Hadamard-basis disagreement have respectively the bit-error and phase-error effects of a Bell measurement. Equality of effects gives equality of these probabilities for every density operator. This identifies the diagnostic probabilities used in the security argument; it makes no assertion about equality of postmeasurement states.
-- source:
--   Simple Proof of Security of the BB84 Quantum Key Distribution Protocol, arXiv:quant-ph/0003004v2, PDF p. 3, Unnumbered Bell-projector identities and check-error interpretation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17

namespace QAlgorithms.Papers.Independent.Intakenext100.P17

noncomputable section

open scoped ComplexConjugate

open Classical

open QAlgorithms.DopedTomography (bellVector)

open QAlgorithms.Papers.Independent.Support50.P04 (BinaryWord)

/-- PDF p.3, the two unnumbered displayed Bell-projector identities.
These are identities of marginal error effects, hence give the same Born error
probabilities for every density operator, including coherent Bell off-diagonal terms.
They assert neither joint measurement of incompatible bases nor equality of the
corresponding postmeasurement states. The frozen bellVector on two one-qubit
registers gives Psi+, i Psi-, Phi- for the Pauli labels X, Y, Z respectively;
the global phase i disappears in pureDensity. The first register is Alice's. -/
theorem bell_check_identities :
    (pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.X)) + pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.Y)) =
      pureDensity (ket (((fun _ => false), (fun _ => true)) : Qubits 1 × Qubits 1)) +
        pureDensity (ket (((fun _ => true), (fun _ => false)) : Qubits 1 × Qubits 1))) ∧
    (pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.Z)) + pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.Y)) =
      pureDensity (xPair false true) + pureDensity (xPair true false)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P17
