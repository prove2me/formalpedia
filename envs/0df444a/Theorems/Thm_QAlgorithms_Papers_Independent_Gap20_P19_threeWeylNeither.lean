-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_threeWeylNeither
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.threeWeylNeither
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:39:02.393391+00:00
-- url     : https://prove2.me/theorems/746e27d2-4e74-4128-a1f2-7faab6a6848f
-- title:
--   Corollary 16
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   For qutrit shift and clock matrices $X,Z$, let $a_0,a_1,a_2>0$ sum to one and not all be equal. Set $T_a(\rho)=a_0\rho+a_1X\rho X^\dagger+a_2Z\rho Z^\dagger$. Then
--   $$T_a\text{ is neither degradable nor antidegradable}.$$
--
--   The unequal-weight condition concerns antidegradability; no derived coherent-information lower bound is assumed.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 22, Corollary 16

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

/-- Corollary 16, PDF pp.22–23. Positive probabilities sum to one and are
not all equal; positive coherent information is a consequence, not a hypothesis. -/
theorem threeWeylNeither (a0 a1 a2 : ℝ) (h0 : 0 < a0) (h1 : 0 < a1)
    (h2 : 0 < a2) (hsum : a0+a1+a2 = 1) (hne : ¬ (a0 = a1 ∧ a1 = a2)) :
    ¬ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (threeWeyl a0 a1 a2) ∧ IsDegradable witness) ∧ ¬ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (threeWeyl a0 a1 a2) ∧ IsAntidegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
