-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_wernerHolevoStructure
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.wernerHolevoStructure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:44:39.881423+00:00
-- url     : https://prove2.me/theorems/eefb7651-12bd-4741-af29-0cba59d430fb
-- title:
--   §2.2: self-complementary Werner–Holevo qutrit channel
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   For $d>1$, define $W_d(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$, extending the source's formula linearly. Every unit pure input has output rank $d-1$. In dimension three the isometry $U_{(b,e),a}=\varepsilon_{bea}/\sqrt2$, where $\varepsilon$ is the three-dimensional Levi-Civita tensor, has both marginals equal to $W_3$, and
--   $$W_3=W_3^C,\qquad W_3\text{ is degradable, antidegradable, and an extreme CPTP map}.$$
--
--   This is a concrete channel with no full-rank pure output.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 10, §2.2: self-complementary Werner–Holevo qutrit channel

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

/-- Section 2.2, PDF p.10: pure-output rank in every d>1 and the specific
self-complementary extreme Werner–Holevo qutrit channel. The complement is tied
to its antisymmetric Levi-Civita isometry, not freely selected. -/
theorem wernerHolevoStructure :
    (∀ d : ℕ, 1 < d → ∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
      (wernerHolevo d (pureDensity psi)).rank = d-1) ∧
    IsIsometry wernerIsometry ∧ receiverChannel wernerIsometry = wernerHolevo 3 ∧
    complementaryChannel wernerIsometry = wernerHolevo 3 ∧
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (wernerHolevo 3) ∧ IsDegradable witness) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (wernerHolevo 3) ∧ IsAntidegradable witness) ∧
    ExtremeIn IsChannel (wernerHolevo 3) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
