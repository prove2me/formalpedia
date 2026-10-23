-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_equalDimensionsLargeEnvironment
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.equalDimensionsLargeEnvironment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:46:58.872715+00:00
-- url     : https://prove2.me/theorems/4502e578-a8b0-4321-a49f-244e12966c10
-- title:
--   §2.3: equal input/output dimensions with larger environment
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $d>1$ and let $N:M_d\to M_d$ have Choi rank $d^2$. Let $F_N(\rho)=\tfrac12|0\rangle\langle0|\otimes\rho+\tfrac12|1\rangle\langle1|\otimes N(\rho)$, and let $S:M_6\to M_3$ be the channel from the symmetric-subspace inclusion into $\mathbb C^3\otimes\mathbb C^3$. The explicitly regrouped tensor dilation of $F_N\otimes S$ is degradable and has
--   $$d_A=d_B=6d,\qquad r(F_N\otimes S)=3(d^2+1)>6d.$$
--
--   This gives equal input/output dimensions with a larger minimum environment.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 11, §2.3: equal input/output dimensions with larger environment

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

/-- Section 2.3, PDF p.11: explicit tensor construction with equal input/output
size 6d and larger minimum environment 3(d^2+1), for d>1. -/
theorem equalDimensionsLargeEnvironment [Nonempty A] [Nonempty E]
    (U : Matrix (A × E) A ℂ) (hU : IsIsometry U)
    (hd : 1 < Fintype.card A) (hfull : (choi (receiverChannel U)).rank = Fintype.card A^2) :
    let V := tensorDilation (flaggedDilation (1/2) U) symmetricIsometry
    IsDegradable V ∧
    Fintype.card (A × Fin 6) = 6*Fintype.card A ∧
    Fintype.card ((Bool × A) × Fin 3) = 6*Fintype.card A ∧
    (choi (receiverChannel V)).rank = 3*(Fintype.card A^2+1) ∧
    6*Fintype.card A < (choi (receiverChannel V)).rank := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
