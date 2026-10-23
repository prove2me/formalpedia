-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_antidegradablePostprocessing
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.antidegradablePostprocessing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:39:57.008019+00:00
-- url     : https://prove2.me/theorems/d3e6ea10-b8d7-46f6-a82a-71ffe74f7c6d
-- title:
--   Lemma 17
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\Gamma:\mathcal B(H_A)\to\mathcal B(H_B)$ be antidegradable and let $\Delta:\mathcal B(H_B)\to\mathcal B(H_C)$ be any channel. Then
--   $$\Delta\circ\Gamma\text{ is antidegradable}.$$
--
--   The conclusion allows arbitrary nonzero finite dimensions and arbitrary CPTP postprocessing.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 27, Lemma 17

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

/-- Lemma 17, PDF p.27: arbitrary CPTP postprocessing and dimensions. -/
theorem antidegradablePostprocessing [Nonempty A] [Nonempty B] [Nonempty C]
    (Gamma : Superop A B) (Delta : Superop B C)
    (hGamma : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Gamma ∧ IsAntidegradable witness)) (hDelta : IsChannel Delta) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (Delta ∘ Gamma) ∧ IsAntidegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
