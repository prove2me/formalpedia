-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_fullRankPureOutput
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.fullRankPureOutput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:28:57.879259+00:00
-- url     : https://prove2.me/theorems/7fbe282c-d7c1-4c77-a4e5-bf93242075ba
-- title:
--   Theorem 3
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $U:H_A\to H_B\otimes H_E$ be a minimal dilation of a degradable channel $\Phi$. Suppose some unit vector $\psi$ has $\operatorname{rank}\Phi(|\psi\rangle\langle\psi|)=d_B$. Then
--   $$d_E=d_B.$$
--
--   This identifies the minimal environment dimension when one pure output has full rank. The printed expression $\operatorname{rank}\Phi(\rho)$ is corrected to $\operatorname{rank}\rho$, with $\rho=\Phi(|\psi\rangle\langle\psi|)$, as in the proof.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 9, Theorem 3

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

/-- Theorem 3, PDF p.9. Printed rank Phi(rho)=d_B is corrected to rank rho=d_B,
as required by rho=Phi(|psi><psi|) and the m=1 proof using Lemma 2. -/
theorem fullRankPureOutput [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (hmin : MinimalDilation (receiverChannel U) U)
    (hfull : ∃ psi : EuclideanSpace ℂ A, IsState psi ∧
      (receiverChannel U (pureDensity psi)).rank = Fintype.card B) :
    Fintype.card E = Fintype.card B := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
