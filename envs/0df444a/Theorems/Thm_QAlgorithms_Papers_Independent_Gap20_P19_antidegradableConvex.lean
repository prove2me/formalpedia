-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_antidegradableConvex
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.antidegradableConvex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:40:40.600285+00:00
-- url     : https://prove2.me/theorems/cd8a39c8-a171-40a0-8ded-b4273b837557
-- title:
--   Theorem 18
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   For antidegradable channels $\Phi,\Psi$ with the same input and output spaces, and every $p\in[0,1]$,
--   $$p\Phi+(1-p)\Psi\text{ is antidegradable}.$$
--
--   This is convexity of the complete set, with no common-environment or common-Kraus-length requirement.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 27, Theorem 18

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

/-- Theorem 18, PDF p.27: convexity, including p=0 and p=1. -/
theorem antidegradableConvex [Nonempty A] [Nonempty B]
    (Phi Psi : Superop A B) (hPhi : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) (hPsi : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Psi ∧ IsAntidegradable witness))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (fun rho => (p : ℂ) • Phi rho + ((1-p : ℝ) : ℂ) • Psi rho) ∧ IsAntidegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
