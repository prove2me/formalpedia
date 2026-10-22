-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_receiver_merging_generation
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.receiver_merging_generation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:21:41.830262+00:00
-- url     : https://prove2.me/theorems/62d1159d-3f3c-4201-920d-d9735b36abc4
-- title:
--   Theorem 7: simultaneous AC and BC entanglement using receiver state merging
-- statement:
--   Let $\mathcal N:A'\to BC$ be a finite-dimensional CPTP broadcast channel on positive-dimensional systems. Let $|\psi\rangle^{AA'}$ be a unit pure reference/input state and put $\sigma=(\mathrm{id}_A\otimes\mathcal N)(\psi)$. For any nonnegative rates $Q_C,Q_{BC}$ with
--
--   $$Q_C<I(A\rangle BC)_\sigma,\qquad I(B\rangle C)_\sigma>0,\qquad Q_{BC}<I(B\rangle C)_\sigma,$$
--
--   there is one protocol generating independent Alice–Charlie and Bob–Charlie EPR resources at those respective rates. Entropies are in bits. For every positive error tolerance and all sufficiently large positive blocklengths, Alice prepares a pure reference/block input, Bob applies a rectangular instrument and sends its classical branch freely to Charlie, and Charlie uses a branch-dependent CPTP decoder. A single joint squared-fidelity test to the product of the two floor-exponential-rank EPRs succeeds with error at most the tolerance. No initial shared entanglement or other side communication is supplied. This retains the second independent resource in the same one-way receiver-assisted protocol.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 13, Theorem 7: simultaneous AC and BC entanglement using receiver state merging

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Theorem 7, PDF p.13: BOTH resources in the SAME protocol, strictly below
the two informations, only free one-way Bob-to-Charlie classical communication. -/
theorem receiver_merging_generation [Nonempty A] [Nonempty B] [Nonempty C]
    {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (N : Superop A (B × C)) (hN : IsChannel N)
    (psi : EuclideanSpace ℂ (R × A)) (hp : IsState psi)
    (QC QBC : ℝ) (hQC : 0 ≤ QC) (hQBC : 0 ≤ QBC)
    (hAC : QC < (mergingInformation N psi).1)
    (hpos : 0 < (mergingInformation N psi).2)
    (hBC : QBC < (mergingInformation N psi).2) :
    assistedAchievable N (QC, QBC) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
