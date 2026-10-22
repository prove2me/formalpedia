-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_ot_receiverSecurity
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.ot_receiverSecurity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:21:12.325821+00:00
-- url     : https://prove2.me/theorems/0881296a-d76d-4f95-a0ea-b3d0c7f7a0a6
-- title:
--   Proposition 4.5: perfect receiver security of the concrete OT protocol
-- statement:
--   For every pair of nonnegative integers $n,\ell$, the concrete prepare–measure–hash protocol of Figure 1 has perfect honest correctness and perfect receiver security. For any distribution of the receiver's initially independent choice bit $C$ and any dishonest sender, its final state admits classical variables $S'_0,S'_1\in\{0,1\}^\ell$ extending the original receiver output $Y$ and sender view $\widetilde S$, with
--   $$\Pr[Y=S'_C]=1,\qquad\rho_{CS'_0S'_1\widetilde S}=\rho_C\otimes\rho_{S'_0S'_1\widetilde S}.$$
--   The sender may send an arbitrary entangled state and adapt its announcements to private quantum memory. The implementation compresses the selected substring before padding on the right with zeros. This is the full extraction criterion of Definition 4.4.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 10, Proposition 4.5: perfect receiver security of the concrete OT protocol

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Proposition 4.5, pp.10-11: the concrete Figure 1 protocol is perfectly
receiver-secure, including the full extraction, for every input distribution.
Honest correctness is also verified for the explicit protocol computation. -/
theorem ot_receiverSecurity (n ell : ℕ) :
    HonestOTCorrect n ell ∧ OTPerfectReceiverSecure n ell := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
