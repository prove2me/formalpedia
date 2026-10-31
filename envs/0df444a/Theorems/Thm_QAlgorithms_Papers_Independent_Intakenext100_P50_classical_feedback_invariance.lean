-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_classical_feedback_invariance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.classical_feedback_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:48:45.155214+00:00
-- url     : https://prove2.me/theorems/1c9eda57-4a98-4b83-b7db-af2db7c9a544
-- title:
--   Classical entanglement-assisted capacity is unchanged by feedback
-- statement:
--   Let $\Lambda:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be a fixed finite-dimensional CPTP channel, where $d_{\rm in},d_{\rm out}\ge1$. Each physical forward use applies the same channel and the identity to all other systems. Memories and return registers may be arbitrarily large finite systems. Initial resources are independent of the message, only the sender can condition operations on that message, and the receiver decodes from its own retained systems. Classical feedback permits unlimited noiseless classical communication from receiver to sender; quantum feedback permits unlimited noiseless quantum communication in that direction. Only forward uses are charged.
--
--   Write $C$ for unassisted classical capacity, $C^{\rm FB}$ for classical capacity with classical feedback, $C^{\rm QFB}$ for classical capacity with quantum feedback, $C_E$ for entanglement-assisted classical capacity without feedback, and $C_E^{\rm FB}$ for entanglement-assisted classical capacity with classical feedback. These are operational capacities in bits per use, defined from finite uniform-message codes with average decoding error tending to zero. Entanglement assistance allows arbitrary prior shared density operators.
--
--   Then
--
--   $$C_E^{\rm FB}=C^{\rm QFB}=C_E.$$
--
--   The equality for quantum feedback holds both with and without prior shared entanglement. This identifies the full operational capacity, including achievability, rather than only an upper bound.
--
--   **Formalization Note** The three equalities explicitly cover both quantum-feedback resource conventions. Supremal rates are represented in the extended real numbers; this does not impose an artificial rate cutoff.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 1, §I, Eq. (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF p.1, Eq. (1), with resource simulations on p.3, §III.B:
classical feedback with prior entanglement and quantum feedback with or without
prior entanglement all have the ordinary entanglement-assisted capacity. -/
theorem classical_feedback_invariance {i o : ℕ} (hi : 0 < i) (ho : 0 < o)
    (N : Superop (Fin i) (Fin o)) (hN : IsChannel N) :
    bowenClassicalCapacity N .classical true = bowenClassicalCapacity N .none true ∧
    bowenClassicalCapacity N .quantum false = bowenClassicalCapacity N .none true ∧
    bowenClassicalCapacity N .quantum true = bowenClassicalCapacity N .none true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
