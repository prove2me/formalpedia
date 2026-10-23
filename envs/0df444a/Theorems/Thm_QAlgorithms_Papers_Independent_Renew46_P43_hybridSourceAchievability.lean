-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_hybridSourceAchievability
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.hybridSourceAchievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:53:37.964951+00:00
-- url     : https://prove2.me/theorems/6befab51-d7e5-4591-a451-15c1bdb4887c
-- title:
--   Corollary IV.16: Every (R1,…,Rs,H(Y)) with all lower subset bounds sum_(j∈J)Rj≥H(X(J)|X(Jc)Y) is quantum-Fbar achievable.
-- statement:
--   Consider a finite pure-letter iid multiple source, allowing correlated classical laws and entangled source letters where the model permits them. Quantum rate regions use separate local CPTP encoders and a joint CPTP decoder, with rates converging and the named average half-trace, average-fidelity or entanglement-fidelity error tending to zero. Entanglement fidelity is used only when every sender system is a full matrix algebra. For classical/hybrid senders $X_1,\ldots,X_s,Y$, conditional entropies are evaluated in the computed joint source average, the Y rate is exactly $H(Y)$, and every sender subset, including empty/full, is tested.
--
--   $$
--   \left[\forall J,\ \sum_{j\in J}R_j\ge H(X(J)\mid X(J^c)Y)\right]\Longrightarrow(R_1,\ldots,R_s,H(Y))\in\mathcal R_{q,\bar F}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 55, Corollary IV.16

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Corollary IV.16, PDF pp.55-56: all lower-subset-admissible tuples are achievable.
This uses the valid permutation construction; it does not assert the false display IV.14. -/
theorem hybridSourceAchievability {s : ℕ} (S : HybridSource s) (R : Fin s → ℝ)
    (hR : R ∈ S.lowerRegion) : S.withYRate R ∈ quantumSourceRegion S.multiple := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
