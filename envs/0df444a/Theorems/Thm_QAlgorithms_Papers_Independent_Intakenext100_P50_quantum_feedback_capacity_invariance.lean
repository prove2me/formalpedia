-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_quantum_feedback_capacity_invariance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.quantum_feedback_capacity_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:52:20.384436+00:00
-- url     : https://prove2.me/theorems/474b83ab-ae0e-4705-a159-1f041414e8c1
-- title:
--   Quantum-capacity counterparts of feedback invariance
-- statement:
--   Let $\Lambda:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be a fixed finite-dimensional CPTP channel, where $d_{\rm in},d_{\rm out}\ge1$. Each physical forward use applies the same channel and the identity to all other systems. Memories and return registers may be arbitrarily large finite systems. Initial resources are independent of the message, only the sender can condition operations on that message, and the receiver decodes from its own retained systems. Classical feedback permits unlimited noiseless classical communication from receiver to sender; quantum feedback permits unlimited noiseless quantum communication in that direction. Only forward uses are charged.
--
--   Write $C$ for unassisted classical capacity, $C^{\rm FB}$ for classical capacity with classical feedback, $C^{\rm QFB}$ for classical capacity with quantum feedback, $C_E$ for entanglement-assisted classical capacity without feedback, and $C_E^{\rm FB}$ for entanglement-assisted classical capacity with classical feedback. These are operational capacities in bits per use, defined from finite uniform-message codes with average decoding error tending to zero. Entanglement assistance allows arbitrary prior shared density operators.
--
--   Let $Q_E$ be quantum capacity with prior entanglement and no feedback, $Q_E^{\rm FB}$ the corresponding capacity with classical feedback, and $Q^{\rm QFB}$ quantum capacity with quantum feedback. Quantum rates are in qubits per use. Their operational codes transmit $k$ logical qubits using $n$ forward uses, with entanglement fidelity tending to one; the shared resource is independent of the logical input and the reference is untouched. Then
--
--   $$Q_E=\tfrac12 C_E,\qquad Q_E^{\rm FB}=Q_E=Q^{\rm QFB},\qquad Q_E^{\rm FB}=\tfrac12 C_E^{\rm FB}.$$
--
--   The quantum-feedback equality holds both with and without prior entanglement. These are asymptotic rate identities: they do not assert exact finite-block conversion for arbitrary integer message dimensions.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 1, §I and §§IV–V, PDF pp.1, 4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF p.1 and pp.4–5: asymptotic quantum counterparts of Eq. (1).
The factor of two is a rate identity, not an exact finite-block dimension transfer. -/
theorem quantum_feedback_capacity_invariance {i o : ℕ}
    (hi : 0 < i) (ho : 0 < o) (N : Superop (Fin i) (Fin o)) (hN : IsChannel N) :
    bowenQuantumCapacity N .none true = ((1 / 2 : ℝ) : EReal) * bowenClassicalCapacity N .none true ∧
    bowenQuantumCapacity N .classical true = bowenQuantumCapacity N .none true ∧
    bowenQuantumCapacity N .classical true =
      ((1 / 2 : ℝ) : EReal) * bowenClassicalCapacity N .classical true ∧
    bowenQuantumCapacity N .quantum false = bowenQuantumCapacity N .none true ∧
    bowenQuantumCapacity N .quantum true = bowenQuantumCapacity N .none true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
