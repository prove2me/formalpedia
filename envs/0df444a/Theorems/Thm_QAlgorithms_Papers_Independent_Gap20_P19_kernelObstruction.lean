-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_kernelObstruction
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.kernelObstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:42:40.418261+00:00
-- url     : https://prove2.me/theorems/2c76329d-35fc-46bd-b853-893f7f5a6985
-- title:
--   §2.1: kernel obstruction (8)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\Phi,\Phi^C$ be the two channels of one isometric dilation and suppose $\Phi$ is degradable. Then
--   $$\Phi(X)=0\Longrightarrow\Phi^C(X)=0\quad\text{for every matrix }X.$$
--
--   Equivalently, $\ker\Phi\subseteq\ker\Phi^C$. The input is an arbitrary operator, not only a density matrix.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 7, §2.1: kernel obstruction (8)

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

/-- Section 2.1, PDF p.7, (8): kernel inclusion on every matrix. -/
theorem kernelObstruction [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U) :
    ∀ rho, receiverChannel U rho = 0 → complementaryChannel U rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
