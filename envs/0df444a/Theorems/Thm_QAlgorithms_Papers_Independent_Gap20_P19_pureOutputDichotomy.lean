-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_pureOutputDichotomy
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.pureOutputDichotomy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:27:11.128145+00:00
-- url     : https://prove2.me/theorems/0aaef4c1-45e8-4644-9868-7110e8886acb
-- title:
--   Theorem 1
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\Phi:M_{d_A}\to M_{d_B}$ map every normalized pure state to a pure state. Then either
--   $$d_A\le d_B,\quad \Phi(\rho)=U\rho U^\dagger,\quad U^\dagger U=I,\quad r(\Phi)=1,$$
--   and $\Phi$ is degradable; or there is a fixed unit vector $\phi$ with $\Phi(\rho)=\operatorname{Tr}(\rho)|\phi\rangle\langle\phi|$ for every operator $\rho$, and $\Phi$ is antidegradable. The alternatives need not be disjoint when $d_A=1$.
--
--   This identifies all pure-state-preserving channels.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 7, Theorem 1

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

/-- Theorem 1, PDF pp.7–8. The fixed-pure-output alternative includes
one-dimensional input; no nonconstant-channel assumption is imposed. -/
theorem pureOutputDichotomy [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (hpure : ∀ psi : EuclideanSpace ℂ A, IsState psi → IsPure (Phi (pureDensity psi))) :
    (Fintype.card A ≤ Fintype.card B ∧
      (∃ U : Matrix B A ℂ, IsIsometry U ∧ Phi = conjSuperop U) ∧
      (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness) ∧ (choi Phi).rank = 1) ∨
    (∃ phi : EuclideanSpace ℂ B, IsState phi ∧
      (∀ rho, Phi rho = rho.trace • pureDensity phi) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
