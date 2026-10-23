-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_twoPauliThreshold
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.twoPauliThreshold
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:54:56.652716+00:00
-- url     : https://prove2.me/theorems/5eff160d-a56f-4b2c-8c10-2a1a7f83159c
-- title:
--   B.4: two-Pauli antidegradability and EB thresholds
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   For $0<s\le1/2$, put $a=(\sqrt{1-2s},\sqrt s,\sqrt s,0)$ and $P_s(\rho)=\sum_k a_k^2\sigma_k\rho\sigma_k$. Then
--   $$P_s\text{ is antidegradable}\iff\tfrac16\le s\le\tfrac12,\qquad P_s\text{ is EB}\iff\tfrac14\le s\le\tfrac12.$$
--   At $s=1/6$ the multipliers are $(2/3,2/3,1/3)$. Their orbit under coordinate permutations and simultaneous sign changes of two coordinates consists of exactly 12 triples; every corresponding unital diagonal qubit map is an extreme point of the antidegradable channels.
--
--   This displays antidegradable channels beyond the EB range.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 35, B.4: two-Pauli antidegradability and EB thresholds

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

/-- Appendix B.4, PDF p.35: both thresholds, explicit boundary multipliers,
and the 12 extreme antidegradable Pauli maps obtained by the stated symmetries. -/
theorem twoPauliThreshold (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1/2) :
    ((∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap (twoPauliAmplitudes s)) ∧ IsAntidegradable witness) ↔ 1/6 ≤ s ∧ s ≤ 1/2) ∧
    (ChannelEB (qubitPauliMap (twoPauliAmplitudes s)) ↔ 1/4 ≤ s ∧ s ≤ 1/2) ∧
    pauliMultipliers (twoPauliAmplitudes (1/6)) = ![2/3,2/3,1/3] ∧
    twoPauliOrbit.Finite ∧ twoPauliOrbit.ncard = 12 ∧
    (∀ lam ∈ twoPauliOrbit, ExtremeIn (fun Phi => ∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness) (multiplierChannel lam)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
