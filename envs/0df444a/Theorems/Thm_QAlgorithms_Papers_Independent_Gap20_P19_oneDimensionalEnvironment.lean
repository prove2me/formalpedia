-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_oneDimensionalEnvironment
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.oneDimensionalEnvironment
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:43:58.920823+00:00
-- url     : https://prove2.me/theorems/d84c1bee-b264-4613-98d5-937ba486cb70
-- title:
--   §2.1: one-dimensional environment bullet
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $r(\Phi)=1$ for a channel $\Phi:M_{d_A}\to M_{d_B}$. There is an isometry $V$ with
--   $$V^\dagger V=I,\qquad\Phi(\rho)=V\rho V^\dagger,\qquad d_A\le d_B.$$
--   The corresponding one-dimensional-environment dilation has complement $\rho\mapsto\operatorname{Tr}\rho$. The trace from the receiver is a CPTP degrader, so $\Phi$ is degradable.
--
--   This uses minimum environment dimension one, not a padded representation.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 7, §2.1: one-dimensional environment bullet

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

/-- Section 2.1, PDF p.7: minimum environment dimension one gives an isometry,
trace complement, and the explicit trace degrader. -/
theorem oneDimensionalEnvironment [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) (hrank : (choi Phi).rank = 1) :
    Fintype.card A ≤ Fintype.card B ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness) ∧
    ∃ V : Matrix B A ℂ, IsIsometry V ∧ Phi = conjSuperop V ∧
      let U : Matrix (B × Fin 1) A ℂ := fun be a => V be.1 a
      complementaryChannel U = (fun rho _ _ => rho.trace) ∧
      IsChannel (fun rho : Matrix B B ℂ => (fun _ _ : Fin 1 => rho.trace)) ∧
      (∀ rho, (Phi rho).trace = rho.trace) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
