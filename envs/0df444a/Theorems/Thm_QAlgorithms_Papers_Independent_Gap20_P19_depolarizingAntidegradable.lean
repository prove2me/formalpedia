-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_depolarizingAntidegradable
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.depolarizingAntidegradable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:55:38.297263+00:00
-- url     : https://prove2.me/theorems/c65146f1-3612-4628-aa8f-374f7b5e03e5
-- title:
--   B.5: depolarizing-channel antidegradability
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $L_\lambda$ be a CPTP depolarizing qubit map fixing $I$ and sending each Pauli matrix to $\lambda\sigma_k$. If $|\lambda|\le2/3$, then
--   $$L_\lambda\text{ is antidegradable}.$$
--
--   This is the sufficient assertion in B.5; the CPTP hypothesis excludes unphysical negative multipliers.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 35, B.5: depolarizing-channel antidegradability

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- Appendix B.5, PDF pp.35–36: the stated sufficient range.
CPTP is explicit; |lam|≤2/3 alone admits unphysical negative multipliers. -/
theorem depolarizingAntidegradable (lam : ℝ)
    (hPhi : IsChannel (multiplierChannel ![lam,lam,lam])) (hlam : |lam| ≤ 2/3) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (multiplierChannel ![lam,lam,lam]) ∧ IsAntidegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
