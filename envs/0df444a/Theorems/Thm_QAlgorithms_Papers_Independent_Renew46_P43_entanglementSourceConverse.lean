-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_entanglementSourceConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.entanglementSourceConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:47:51.408702+00:00
-- url     : https://prove2.me/theorems/ca22a5d1-09de-45d6-bc2b-33d3b00f0449
-- title:
--   Theorem IV.7: For fully quantum multiple source, any quantum-Fe achievable R obeys every sum_(i∈I)Ri≥H(A(I)|A(Ic))=H(averageState)−H(averageStat
-- statement:
--   Consider a finite pure-letter iid multiple source, allowing correlated classical laws and entangled source letters where the model permits them. Quantum rate regions use separate local CPTP encoders and a joint CPTP decoder, with rates converging and the named average half-trace, average-fidelity or entanglement-fidelity error tending to zero. Entanglement fidelity is used only when every sender system is a full matrix algebra. For classical/hybrid senders $X_1,\ldots,X_s,Y$, conditional entropies are evaluated in the computed joint source average, the Y rate is exactly $H(Y)$, and every sender subset, including empty/full, is tested.
--
--   $$
--   \forall J\subseteq[s]:\quad\sum_{i\in J}R_i\ge H(\bar\rho)-H(\bar\rho_{J^c}).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 50, Theorem IV.7

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

/-- Theorem IV.7, PDF pp.50-51: every subset, empty and full included; no sender
product-state promise or independent sender-law assumption. -/
theorem entanglementSourceConverse {s : ℕ} {L : Type*} [Fintype L]
    (S : MultipleData s L) (hS : S.Valid)
    (hfull : ∀ i a b, (S.system i).block a = (S.system i).block b)
    (R : Fin s → ℝ) (hR : R ∈ entanglementSourceRegion S hfull) :
    ∀ J : Finset (Fin s), ∑ i ∈ J, R i ≥
      vnEntropy S.average - vnEntropy (multipleMarginal S.system S.average Jᶜ) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
