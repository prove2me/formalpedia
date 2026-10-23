-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_coDegradableFlags
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.coDegradableFlags
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:48:05.123622+00:00
-- url     : https://prove2.me/theorems/cec446ff-a02e-46cf-8e85-b777e61590e9
-- title:
--   §2.3: co-degradable pair construction (24)–(25)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $M,N$ have isometric dilations with possibly different environments. Suppose CPTP maps $X,Y$ satisfy $X\circ N=M^C$ and $Y\circ M=N^C$ on every operator. Then the normalized sum-flag dilation realizes
--   $$F(\rho)=\tfrac12|0\rangle\langle0|\otimes M(\rho)+\tfrac12|1\rangle\langle1|\otimes N(\rho),$$
--   is degradable, and $r(F)=r(M)+r(N)$.
--
--   The cross-degrading maps are assumptions on the pair. No existence assertion about additional co-degradable pairs is made.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 11, §2.3: co-degradable pair construction (24)–(25)

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

/-- Section 2.3, PDF p.11, (24)–(25): cross-degraders are hypotheses on
the pair; their environments remain distinct. Minimal Kraus ranks add. -/
theorem coDegradableFlags [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F]
    (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ)
    (hU : IsIsometry U) (hV : IsIsometry V)
    (X : Superop B E) (Y : Superop B F) (hX : IsChannel X) (hY : IsChannel Y)
    (hcrossX : ∀ rho, X (receiverChannel V rho) = complementaryChannel U rho)
    (hcrossY : ∀ rho, Y (receiverChannel U rho) = complementaryChannel V rho) :
    receiverChannel (coFlagDilation U V) = coFlags (receiverChannel U) (receiverChannel V) ∧
    IsDegradable (coFlagDilation U V) ∧
    (choi (coFlags (receiverChannel U) (receiverChannel V))).rank =
      (choi (receiverChannel U)).rank+(choi (receiverChannel V)).rank := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
