-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_symmetricSelfComplement
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.symmetricSelfComplement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:46:22.131204+00:00
-- url     : https://prove2.me/theorems/0a70d8d6-6cec-4ed8-91af-8807911fbecc
-- title:
--   §2.3: symmetric-subspace channel (23)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $V:\mathbb C^6\to\mathbb C^3\otimes\mathbb C^3$ send a standard basis to the three diagonal vectors and the three normalized symmetric off-diagonal vectors. Then
--   $$V^\dagger V=I,\quad VV^\dagger=(I+\mathrm{Swap})/2,\quad S(\rho)=\operatorname{Tr}_E(V\rho V^\dagger)=S^C(\rho).$$
--   The channel $S$ is both degradable and antidegradable, with Choi rank three.
--
--   This constructs the source's symmetric-subspace example rather than assuming self-complementarity of an unrelated channel.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 11, §2.3: symmetric-subspace channel (23)

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

/-- Section 2.3, PDF p.11, (23): the constructed symmetric-subspace map
has equal marginals and is both classes; its Choi rank is three. -/
theorem symmetricSelfComplement :
    IsIsometry symmetricIsometry ∧
    (∀ p q, (symmetricIsometry * symmetricIsometryᴴ) p q =
      (1/2 : ℂ)*((if p=q then 1 else 0)+(if p=(q.2,q.1) then 1 else 0))) ∧
    complementaryChannel symmetricIsometry = symmetricSubspaceMap ∧
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = symmetricSubspaceMap ∧ IsDegradable witness) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = symmetricSubspaceMap ∧ IsAntidegradable witness) ∧
    (choi symmetricSubspaceMap).rank = 3 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
