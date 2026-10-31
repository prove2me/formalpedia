-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_quantum_feedback_information_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.quantum_feedback_information_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:49:24.059976+00:00
-- url     : https://prove2.me/theorems/5b2c2381-a492-43fa-a63b-7b6059204a18
-- title:
--   Quantum-feedback information bound for n forward uses
-- statement:
--   Let $\Lambda:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be a fixed finite-dimensional CPTP channel, where $d_{\rm in},d_{\rm out}\ge1$. Each physical forward use applies the same channel and the identity to all other systems. Memories and return registers may be arbitrarily large finite systems. Initial resources are independent of the message, only the sender can condition operations on that message, and the receiver decodes from its own retained systems. Classical feedback permits unlimited noiseless classical communication from receiver to sender; quantum feedback permits unlimited noiseless quantum communication in that direction. Only forward uses are charged.
--
--   Fix $n\ge0$, a finite message alphabet of size $m\ge1$, and a normalized prior $p_x\ge0$ with $\sum_xp_x=1$. Let an arbitrary legal quantum-feedback protocol start with a message-independent shared density operator $\sigma_{A_0B_0}$. If $\rho_x^{B_f}$ is Bob's retained density after the protocol, define
--
--   $$I(M:B_f)=S\!\left(\sum_xp_x\rho_x^{B_f}\right)-\sum_xp_xS(\rho_x^{B_f}),$$
--
--   where $S$ is von Neumann entropy in bits, with $0\log_20=0$. Define $J(\Lambda)$ as the supremal value of $I(M:A_{\rm out}\mid B)$ over all finite normalized ensembles of input–auxiliary density operators $\tau_x^{A_{\rm in}B}$, after applying $\Lambda$ to $A_{\rm in}$. The auxiliary dimension and the ensemble alphabet are unrestricted finite dimensions. Then
--
--   $$I(M:B_f)\le nJ(\Lambda).$$
--
--   This is an additive information bound on the receiver's actual retained state. The external classical reference $M$ is unchanged throughout the protocol.
--
--   **Formalization Note** The input port has dimension $d_{\rm in}$ and the output port dimension $d_{\rm out}$. Conditional information is the output ensemble's Holevo information minus that of its $B$ marginal. No common conditional density for all messages is imposed.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 2, §III.A, Lemma 1, Eq. (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF pp.2–3, Lemma 1, Eq. (7): Bob's retained cq information after
n actual uses is at most n times the single-use conditional information maximum.
The arbitrary normalized prior need not be uniform. -/
theorem quantum_feedback_information_bound {i o m n : ℕ}
    (hi : 0 < i) (ho : 0 < o) (hm : 0 < m)
    (N : Superop (Fin i) (Fin o)) (hN : IsChannel N)
    (P : BowenFeedbackProtocol i o m n) (hP : P.Legal .quantum)
    (X : Matrix (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) ℂ)
    (hX : IsDensityMatrix X) (p : Fin m → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    (bowenCqInformation p (fun x => P.receiver .quantum N x X) : EReal) ≤
      ((n : ℝ) : EReal) * maxConditionalInformation N := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
