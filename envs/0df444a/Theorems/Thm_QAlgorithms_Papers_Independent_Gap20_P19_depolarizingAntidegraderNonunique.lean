-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_depolarizingAntidegraderNonunique
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.depolarizingAntidegraderNonunique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:56:25.174025+00:00
-- url     : https://prove2.me/theorems/7b0ddff2-9597-46bc-98a7-02cc391b7282
-- title:
--   B.5: nonuniqueness of complementary degraders
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $-1/3<\lambda<2/3$ and put $a_0=\sqrt{(1+3\lambda)/4}$ and $a_1=a_2=a_3=\sqrt{(1-\lambda)/4}$. Fix the dilation of $P_a$ given by the four Kraus operators $a_k\sigma_k$, with complement $P_a^C$. There exist two distinct CPTP maps $D_1,D_2:M_4\to M_2$ such that
--   $$D_1\circ P_a^C=P_a=D_2\circ P_a^C.$$
--
--   Distinctness is on the same full complementary operator space. No uniqueness claim is made at either endpoint.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 35, B.5: nonuniqueness of complementary degraders

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

/-- Appendix B.5, PDF pp.35–36: distinct CPTP antidegraders on the SAME
fixed complementary output for -1/3<lam<2/3. No endpoint uniqueness is asserted. -/
theorem depolarizingAntidegraderNonunique (lam : ℝ)
    (hlo : -1/3 < lam) (hhi : lam < 2/3) :
    let a := depolarizingAmplitudes lam
    let U := indexedKrausDilation (pauliKraus a)
    ∃ D1 D2 : Superop (Fin 4) Bool, IsChannel D1 ∧ IsChannel D2 ∧ D1 ≠ D2 ∧
      (∀ rho, D1 (complementaryChannel U rho) = qubitPauliMap a rho) ∧
      (∀ rho, D2 (complementaryChannel U rho) = qubitPauliMap a rho) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
