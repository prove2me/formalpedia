-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_flaggedIdentityDegradable
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.flaggedIdentityDegradable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:45:36.689981+00:00
-- url     : https://prove2.me/theorems/c17563f0-c248-41c3-84bc-9dbd2c612b57
-- title:
--   §2.3: degradable flagged identity/noise family (16)–(22)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $N:M_d\to M_d$ be given by an isometric dilation $U$, and let $1/2\le x\le1$. Define
--   $$F_{x,N}(\rho)=x|0\rangle\langle0|\otimes\rho+(1-x)|1\rangle\langle1|\otimes N(\rho).$$
--   Its normalized flag dilation has complement $x\operatorname{Tr}\rho\oplus(1-x)N^C(\rho)$. On receiver blocks $\gamma_0,\gamma_1$, the CPTP degrader is
--   $$D_x(\gamma)=\left(\frac{2x-1}{x}\operatorname{Tr}\gamma_0+\operatorname{Tr}\gamma_1\right)\oplus\frac{1-x}{x}N^C(\gamma_0),$$
--   with flag coherences discarded. Thus $D_xF_{x,N}=F_{x,N}^C$ and $F_{x,N}$ is degradable. At $x=1/2$, its Choi rank is $1+r(N)$; for $d>1$ and $r(N)=d^2$, this exceeds output dimension $2d$.
--
--   Scalar-first complement ordering is used consistently, including $x=1$.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 10, §2.3: degradable flagged identity/noise family (16)–(22)

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

/-- Section 2.3, PDF pp.10–11, (16)–(22): corrected weights, normalized
common dilation, explicit degrader and minimal-rank enlargement at x=1/2.
At x=1 the noise Kraus operators vanish, so no 1+r_N rank assertion is made. -/
theorem flaggedIdentityDegradable [Nonempty A] [Nonempty E]
    (U : Matrix (A × E) A ℂ) (hU : IsIsometry U)
    (x : ℝ) (hx0 : 1/2 ≤ x) (hx1 : x ≤ 1) :
    receiverChannel (flaggedDilation x U) = flaggedIdentity x (receiverChannel U) ∧
    complementaryChannel (flaggedDilation x U) = flaggedComplement x U ∧
    IsDegradable (flaggedDilation x U) ∧ IsChannel (flaggedDegrader x U) ∧
    (∀ rho, flaggedDegrader x U (flaggedIdentity x (receiverChannel U) rho) =
      flaggedComplement x U rho) ∧
    (choi (flaggedIdentity (1/2) (receiverChannel U))).rank = 1+(choi (receiverChannel U)).rank ∧
    (1 < Fintype.card A → (choi (receiverChannel U)).rank = Fintype.card A^2 →
      2*Fintype.card A < (choi (flaggedIdentity (1/2) (receiverChannel U))).rank) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
