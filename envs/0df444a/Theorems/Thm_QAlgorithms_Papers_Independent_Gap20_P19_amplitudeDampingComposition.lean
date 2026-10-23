-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_amplitudeDampingComposition
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.amplitudeDampingComposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:51:56.068611+00:00
-- url     : https://prove2.me/theorems/3ce881c7-a5d4-422e-bc00-03f4d824ce51
-- title:
--   B.2: amplitude-damping composition
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Write $\Phi(u,v)(\rho)=A_+\rho A_+^\dagger+A_-\rho A_-^\dagger$, where $A_+=\operatorname{diag}(\cos((v-u)/2),\cos((u+v)/2))$ and $A_-=\begin{pmatrix}0&\sin((u+v)/2)\\\sin((v-u)/2)&0\end{pmatrix}$. These normalized operators give the Bloch map (85); they correct the transposition in printed (39).
--
--   For arbitrary real $u_1,u_2$, set $u_3=\arccos(\cos u_1\cos u_2)$. Then
--   $$\Phi(u_1,u_1)\circ\Phi(u_2,u_2)=\Phi(u_3,u_3).$$
--
--   The amplitude-damping composition law has no divisions and includes its degenerate boundaries.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 29, B.2: amplitude-damping composition

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

/-- Appendix B.2, PDF p.29: amplitude-damping composition, with all real
angles and no division or nonsingularity restriction. -/
theorem amplitudeDampingComposition (u1 u2 : ℝ) :
    rankTwoQubitMap u1 u1 ∘ rankTwoQubitMap u2 u2 =
      rankTwoQubitMap (Real.arccos (Real.cos u1*Real.cos u2))
        (Real.arccos (Real.cos u1*Real.cos u2)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
