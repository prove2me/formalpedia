-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_oneDimensionalOutput
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.oneDimensionalOutput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:43:14.524986+00:00
-- url     : https://prove2.me/theorems/34efe69f-b799-47b8-bd52-8b25720a11b8
-- title:
--   §2.1: one-dimensional output bullet
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Every channel $\Phi:M_{d_A}\to M_1$ is the trace map. Its Choi rank and a canonical Kraus family are
--   $$r(\Phi)=d_A,\qquad H_k=|0\rangle\langle e_k|.$$
--   For the dilation with these row-bra operators the complementary channel is exactly the identity on $M_{d_A}$, and $\Phi$ is antidegradable.
--
--   Fixing this dilation makes the identity-complement statement basis precise.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 7, §2.1: one-dimensional output bullet

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

/-- Section 2.1, PDF p.7: unique scalar-output trace map, its rank and
canonical row-bra Kraus representation, with the corresponding identity complement. -/
theorem oneDimensionalOutput [Nonempty A] (Phi : Superop A (Fin 1))
    (hPhi : IsChannel Phi) :
    let H : A → Matrix (Fin 1) A ℂ := fun k _ a => if a = k then 1 else 0
    Phi = (fun rho _ _ => rho.trace) ∧ Phi = krausApply H ∧
    (choi Phi).rank = Fintype.card A ∧
    complementaryChannel (indexedKrausDilation H) = id ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
