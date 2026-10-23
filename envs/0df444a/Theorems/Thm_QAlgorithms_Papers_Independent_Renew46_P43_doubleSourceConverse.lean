-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_doubleSourceConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.doubleSourceConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:45:44.579535+00:00
-- url     : https://prove2.me/theorems/8dcafeef-4749-4ee0-8004-1c0c646c676e
-- title:
--   Theorem IV.1: Any quantum-Dbar achievable pair has R1+R2≥H(A1A2), R1≥H(A1|A2), R2≥H(A2|A1).
-- statement:
--   Consider a finite pure-letter iid multiple source, allowing correlated classical laws and entangled source letters where the model permits them. Quantum rate regions use separate local CPTP encoders and a joint CPTP decoder, with rates converging and the named average half-trace, average-fidelity or entanglement-fidelity error tending to zero. Entanglement fidelity is used only when every sender system is a full matrix algebra. For classical/hybrid senders $X_1,\ldots,X_s,Y$, conditional entropies are evaluated in the computed joint source average, the Y rate is exactly $H(Y)$, and every sender subset, including empty/full, is tested.
--
--   $$
--   R_1+R_2\ge H(A_1A_2),\qquad R_1\ge H(A_1\mid A_2),\qquad R_2\ge H(A_2\mid A_1).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 47, Theorem IV.1

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

/-- Theorem IV.1, PDF p.47: hybrid systems and entangled letters are allowed.
Conditional entropies can be negative; only the code resources enforce nonnegative rates. -/
theorem doubleSourceConverse {L : Type*} [Fintype L] (S : MultipleData 2 L) (hS : S.Valid)
    (R : Fin 2 → ℝ) (hR : R ∈ quantumSourceRegion S true) :
    R 0 + R 1 ≥ vnEntropy S.average ∧
    R 0 ≥ vnEntropy S.average - vnEntropy (multipleMarginal S.system S.average {1}) ∧
    R 1 ≥ vnEntropy S.average - vnEntropy (multipleMarginal S.system S.average {0}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
