-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_canonicalComplement
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.canonicalComplement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:51:07.344795+00:00
-- url     : https://prove2.me/theorems/8c04cdb2-29d2-4c40-ac16-239312daaed7
-- title:
--   Theorem 19(a), separately retained complementary Bloch map
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Write $\Phi(u,v)(\rho)=A_+\rho A_+^\dagger+A_-\rho A_-^\dagger$, where $A_+=\operatorname{diag}(\cos((v-u)/2),\cos((u+v)/2))$ and $A_-=\begin{pmatrix}0&\sin((u+v)/2)\\\sin((v-u)/2)&0\end{pmatrix}$. These normalized operators give the Bloch map (85); they correct the transposition in printed (39).
--
--   For every real $u,v$, the Kraus pair is normalized and its fixed complementary channel satisfies
--   $$\Phi^C(u,v)=\Phi(v-\pi/2,u-\pi/2).$$
--
--   This retains the independent correct part (a), while the unrestricted prescribed degrader in part (b) remains deferred.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 29, Theorem 19(a), separately retained complementary Bloch map

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

/-- Theorem 19(a), PDF pp.28–29, retained separately from the incorrect part (b).
The complement is fixed by the corrected normalized Kraus pair. -/
theorem canonicalComplement (u v : ℝ) :
    IsKrausFamily (canonicalKraus u v) ∧
    complementaryChannel (indexedKrausDilation (canonicalKraus u v)) =
      rankTwoQubitMap (v-Real.pi/2) (u-Real.pi/2) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
