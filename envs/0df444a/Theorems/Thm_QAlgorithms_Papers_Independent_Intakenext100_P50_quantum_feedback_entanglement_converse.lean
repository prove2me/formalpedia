-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_quantum_feedback_entanglement_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.quantum_feedback_entanglement_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:51:42.995744+00:00
-- url     : https://prove2.me/theorems/bc8196de-fed6-4fc1-9b92-d9eabfd5604b
-- title:
--   Quantum-feedback converse by ordinary entanglement-assisted capacity
-- statement:
--   Let $\Lambda:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be a fixed finite-dimensional CPTP channel, where $d_{\rm in},d_{\rm out}\ge1$. Each physical forward use applies the same channel and the identity to all other systems. Memories and return registers may be arbitrarily large finite systems. Initial resources are independent of the message, only the sender can condition operations on that message, and the receiver decodes from its own retained systems. Classical feedback permits unlimited noiseless classical communication from receiver to sender; quantum feedback permits unlimited noiseless quantum communication in that direction. Only forward uses are charged.
--
--   Write $C$ for unassisted classical capacity, $C^{\rm FB}$ for classical capacity with classical feedback, $C^{\rm QFB}$ for classical capacity with quantum feedback, $C_E$ for entanglement-assisted classical capacity without feedback, and $C_E^{\rm FB}$ for entanglement-assisted classical capacity with classical feedback. These are operational capacities in bits per use, defined from finite uniform-message codes with average decoding error tending to zero. Entanglement assistance allows arbitrary prior shared density operators.
--
--   The capacities satisfy
--
--   $$C^{\rm QFB}\le C_E,\qquad C_E^{\rm FB}\le C_E.$$
--
--   The first bound holds with or without prior entanglement. The second bound includes the sentence following Eq. (19). These converse bounds use ordinary operational entanglement-assisted capacity, with no entropy-concavity or purification inequalities added as hypotheses.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 3, §III.B, Theorem 3, Eq. (19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF pp.3–4, Theorem 3, Eq. (19), including the following sentence:
both quantum-feedback classical capacity and entanglement-assisted classical
capacity with classical feedback are bounded by ordinary EA capacity. -/
theorem quantum_feedback_entanglement_converse {i o : ℕ}
    (hi : 0 < i) (ho : 0 < o) (N : Superop (Fin i) (Fin o)) (hN : IsChannel N) :
    bowenClassicalCapacity N .quantum false ≤ bowenClassicalCapacity N .none true ∧
    bowenClassicalCapacity N .quantum true ≤ bowenClassicalCapacity N .none true ∧
    bowenClassicalCapacity N .classical true ≤ bowenClassicalCapacity N .none true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
