-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_classical_capacity_ordering
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.classical_capacity_ordering
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:09:58.771984+00:00
-- url     : https://prove2.me/theorems/c78f126a-039d-436a-8f1a-db1de21d5074
-- title:
--   Classical capacity ordering and conditional strictness
-- statement:
--   Let $\Lambda:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be a fixed finite-dimensional CPTP channel, where $d_{\rm in},d_{\rm out}\ge1$. Each physical forward use applies the same channel and the identity to all other systems. Memories and return registers may be arbitrarily large finite systems. Initial resources are independent of the message, only the sender can condition operations on that message, and the receiver decodes from its own retained systems. Classical feedback permits unlimited noiseless classical communication from receiver to sender; quantum feedback permits unlimited noiseless quantum communication in that direction. Only forward uses are charged.
--
--   Write $C$ for unassisted classical capacity, $C^{\rm FB}$ for classical capacity with classical feedback, $C^{\rm QFB}$ for classical capacity with quantum feedback, $C_E$ for entanglement-assisted classical capacity without feedback, and $C_E^{\rm FB}$ for entanglement-assisted classical capacity with classical feedback. These are operational capacities in bits per use, defined from finite uniform-message codes with average decoding error tending to zero. Entanglement assistance allows arbitrary prior shared density operators.
--
--   Then
--
--   $$C\le C^{\rm FB}\le C^{\rm QFB}=C_E^{\rm FB}=C_E.$$
--
--   If $C\ne C_E$, at least one of the first two inequalities is strict:
--
--   $$C<C^{\rm FB}\quad\text{or}\quad C^{\rm FB}<C^{\rm QFB}.$$
--
--   This compares the distinct resource regimes without resolving the paper's historical open question about whether classical feedback alone can increase unassisted classical capacity.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 4, §IV, Eq. (27)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF p.4, Eq. (27): classical capacity ordering, all equalities, and
at least one strict inequality whenever unassisted and EA capacities differ. -/
theorem classical_capacity_ordering {i o : ℕ}
    (hi : 0 < i) (ho : 0 < o) (N : Superop (Fin i) (Fin o)) (hN : IsChannel N) :
    bowenClassicalCapacity N .none false ≤ bowenClassicalCapacity N .classical false ∧
    bowenClassicalCapacity N .classical false ≤ bowenClassicalCapacity N .quantum false ∧
    bowenClassicalCapacity N .quantum false = bowenClassicalCapacity N .classical true ∧
    bowenClassicalCapacity N .classical true = bowenClassicalCapacity N .none true ∧
    (bowenClassicalCapacity N .none false ≠ bowenClassicalCapacity N .none true →
      bowenClassicalCapacity N .none false < bowenClassicalCapacity N .classical false ∨
      bowenClassicalCapacity N .classical false < bowenClassicalCapacity N .quantum false) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
