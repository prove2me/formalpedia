-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_hybridSourceConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.hybridSourceConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:54:18.268982+00:00
-- url     : https://prove2.me/theorems/d845b0f1-8ffe-4c29-ad8b-dfb415ccd205
-- title:
--   Theorem IV.17: Every quantum-Fbar achievable (R1,…,Rs,H(Y)) obeys all lower subset bounds sum_(j∈J)Rj≥H(X(J)|X(Jc)Y).
-- statement:
--   Consider a finite pure-letter iid multiple source, allowing correlated classical laws and entangled source letters where the model permits them. Quantum rate regions use separate local CPTP encoders and a joint CPTP decoder, with rates converging and the named average half-trace, average-fidelity or entanglement-fidelity error tending to zero. Entanglement fidelity is used only when every sender system is a full matrix algebra. For classical/hybrid senders $X_1,\ldots,X_s,Y$, conditional entropies are evaluated in the computed joint source average, the Y rate is exactly $H(Y)$, and every sender subset, including empty/full, is tested.
--
--   $$
--   (R_1,\ldots,R_s,H(Y))\in\mathcal R_{q,\bar F}\Longrightarrow\forall J,\ \sum_{j\in J}R_j\ge H(X(J)\mid X(J^c)Y).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 56, Theorem IV.17

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

/-- Theorem IV.17, PDF p.56: the printed theorem allows correlated classical laws.
Its proof invokes III.5 outside that lemma's independence domain; this proof limitation
is recorded without adding independence to the theorem. -/
theorem hybridSourceConverse {s : ℕ} (S : HybridSource s) (R : Fin s → ℝ)
    (hR : S.withYRate R ∈ quantumSourceRegion S.multiple) : R ∈ S.lowerRegion := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
