-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_twistedDiagonalRank
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.twistedDiagonalRank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:35:43.929142+00:00
-- url     : https://prove2.me/theorems/cf517333-0871-49df-b87c-153764e22769
-- title:
--   Theorem 12
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\Phi:M_d\to M_d$ have a normalized Kraus representation $\Phi(\rho)=\sum_k A_k\rho A_k^\dagger$ and invertible matrices $X,Y$ for which every $YA_kX$ is diagonal. Then
--   $$r(\Phi)\le d,\qquad\exists\psi:\ \|\psi\|=1,\quad\operatorname{rank}\Phi(|\psi\rangle\langle\psi|)=r(\Phi).$$
--
--   The second equality corrects the printed $d_B$ to $d_E$, exactly as computed by (54). The identity channel in dimension greater than one disproves the printed version.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 19, Theorem 12

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

/-- Theorem 12, PDF pp.19–20. Corrected printed output rank d_B to d_E:
(54) computes d_E, and the identity channel disproves the printed d_B clause. -/
theorem twistedDiagonalRank [Nonempty A] (Phi : Superop A A)
    (hPhi : IsChannel Phi) (htwist : TwistedDiagonal Phi) :
    (choi Phi).rank ≤ Fintype.card A ∧
    ∃ psi : EuclideanSpace ℂ A, IsState psi ∧
      (Phi (pureDensity psi)).rank = (choi Phi).rank := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
