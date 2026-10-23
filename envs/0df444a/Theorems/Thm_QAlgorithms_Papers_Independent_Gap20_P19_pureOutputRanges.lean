-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_pureOutputRanges
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.pureOutputRanges
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:28:04.142773+00:00
-- url     : https://prove2.me/theorems/cd3b3d10-0a5d-4f28-83c0-46fb218ff2a5
-- title:
--   Lemma 2
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $U:H_A\to H_B\otimes H_E$ be a minimal isometric dilation of a degradable channel $\Phi$, with complement $\Phi^C$. For any finite family of unit vectors $\psi_j$, define vector subspaces $B_j=\operatorname{range}\Phi(|\psi_j\rangle\langle\psi_j|)$ and $E_j=\operatorname{range}\Phi^C(|\psi_j\rangle\langle\psi_j|)$. Then
--   $$\dim B_j=\dim E_j\quad\text{for every }j,\qquad \operatorname{span}\bigcup_j B_j=H_B\Longrightarrow\operatorname{span}\bigcup_j E_j=H_E.$$
--
--   The spanning implication relates output supports to the minimal environment.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 8, Lemma 2

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

/-- Lemma 2, PDF pp.8–9. Bj and Ej are vector subspaces. The common
dilation is minimal, preventing false spanning conclusions after padding. -/
theorem pureOutputRanges [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (hmin : MinimalDilation (receiverChannel U) U) :
    ∀ m : ℕ, ∀ psi : Fin m → EuclideanSpace ℂ A,
      (∀ j, IsState (psi j)) →
      (∀ j, (receiverChannel U (pureDensity (psi j))).rank =
        (complementaryChannel U (pureDensity (psi j))).rank) ∧
      ((⨆ j, matrixRange (receiverChannel U (pureDensity (psi j)))) = ⊤ →
        (⨆ j, matrixRange (complementaryChannel U (pureDensity (psi j)))) = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
