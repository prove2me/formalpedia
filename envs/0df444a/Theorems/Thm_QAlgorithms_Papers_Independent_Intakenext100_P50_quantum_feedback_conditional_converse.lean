-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_quantum_feedback_conditional_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.quantum_feedback_conditional_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:50:59.203054+00:00
-- url     : https://prove2.me/theorems/3c04278d-9a3d-4578-af92-1a707058d488
-- title:
--   One-use conditional-information capacity converse
-- statement:
--   Let $\Lambda:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be a fixed finite-dimensional CPTP channel, where $d_{\rm in},d_{\rm out}\ge1$. Each physical forward use applies the same channel and the identity to all other systems. Memories and return registers may be arbitrarily large finite systems. Initial resources are independent of the message, only the sender can condition operations on that message, and the receiver decodes from its own retained systems. Classical feedback permits unlimited noiseless classical communication from receiver to sender; quantum feedback permits unlimited noiseless quantum communication in that direction. Only forward uses are charged.
--
--   Write $C$ for unassisted classical capacity, $C^{\rm FB}$ for classical capacity with classical feedback, $C^{\rm QFB}$ for classical capacity with quantum feedback, $C_E$ for entanglement-assisted classical capacity without feedback, and $C_E^{\rm FB}$ for entanglement-assisted classical capacity with classical feedback. These are operational capacities in bits per use, defined from finite uniform-message codes with average decoding error tending to zero. Entanglement assistance allows arbitrary prior shared density operators.
--
--   Let $J(\Lambda)$ be the supremum of $I(M:A_{\rm out}\mid B)$ for output cq states
--
--   $$\rho_{MA_{\rm out}B}=\sum_xp_x|x\rangle\langle x|_M\otimes(\Lambda\otimes\operatorname{id}_B)(\tau_x^{A_{\rm in}B}),$$
--
--   where the alphabet and auxiliary register $B$ are arbitrary finite systems, the prior is nonnegative and normalized, and every $\tau_x$ is a density operator. Quantum conditional mutual information and all logarithms are measured in bits. Then, with or without prior entanglement,
--
--   $$C^{\rm QFB}\le J(\Lambda).$$
--
--   This translates the finite-block information bound into a converse for vanishing-error channel coding. The code definition retains its actual CPTP execution and POVM decoding error; it does not assume the converse as a coding axiom.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 3, §III.A, Theorem 2, Eq. (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF p.3, Theorem 2, Eq. (13): the operational quantum-feedback
classical capacity is bounded by the maximum one-use conditional information. -/
theorem quantum_feedback_conditional_converse {i o : ℕ}
    (hi : 0 < i) (ho : 0 < o) (N : Superop (Fin i) (Fin o)) (hN : IsChannel N) :
    bowenClassicalCapacity N .quantum false ≤ maxConditionalInformation N ∧
    bowenClassicalCapacity N .quantum true ≤ maxConditionalInformation N := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
