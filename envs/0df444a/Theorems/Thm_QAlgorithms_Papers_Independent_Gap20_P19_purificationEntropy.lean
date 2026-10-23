-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_purificationEntropy
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.purificationEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:49:40.008274+00:00
-- url     : https://prove2.me/theorems/155cbde3-69ca-495b-989c-027bce59238c
-- title:
--   A.2: purification and complementary-output entropy (69)–(71)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $U:H_A\to H_B\otimes H_E$ be an isometry, with marginals $\Phi,\Phi^C$. For a unit purification vector $\chi\in H_R\otimes H_A$, put $\rho=\operatorname{Tr}_R|\chi\rangle\langle\chi|$. Then
--   $$S[(\mathrm{id}_R\otimes\Phi)(|\chi\rangle\langle\chi|)]=S[\Phi^C(\rho)],$$
--   and consequently the purification definition of coherent information equals $S[\Phi(\rho)]-S[\Phi^C(\rho)]$.
--
--   Entropy is measured consistently in bits. Finite dimensions supply finite output entropies.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 26, A.2: purification and complementary-output entropy (69)–(71)

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

/-- Appendix A.2, PDF p.26, (69)–(71): purification output entropy equals
complement entropy. Both coherent-information definitions consequently agree. -/
theorem purificationEntropy [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (chi : EuclideanSpace ℂ (R × A)) (hchi : IsState chi) :
    let rho := traceLeft (pureDensity chi)
    vnEntropy (idTensorSuperop (receiverChannel U) (pureDensity chi)) =
      vnEntropy (complementaryChannel U rho) ∧
    vnEntropy (receiverChannel U rho) -
      vnEntropy (idTensorSuperop (receiverChannel U) (pureDensity chi)) = coherentAt U rho := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
