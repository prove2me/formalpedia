-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_qutritOutputRank
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.qutritOutputRank
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:34:09.067182+00:00
-- url     : https://prove2.me/theorems/974ff0fe-037f-4b47-86d0-a8bfcb18719c
-- title:
--   Theorem 10
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Every degradable channel $\Phi:M_d\to M_3$, for arbitrary $d\ge1$, satisfies
--   $$r(\Phi)\le3.$$
--
--   This bounds the minimal environment for every qutrit-output degradable channel.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 17, Theorem 10

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

/-- Theorem 10, PDF p.17: arbitrary positive input dimension and qutrit output. -/
theorem qutritOutputRank [Nonempty A] (Phi : Superop A (Fin 3))
    (hPhi : IsChannel Phi) (hdeg : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness)) : (choi Phi).rank ≤ 3 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
