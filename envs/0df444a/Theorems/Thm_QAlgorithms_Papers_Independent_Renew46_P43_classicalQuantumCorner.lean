-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_classicalQuantumCorner
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.classicalQuantumCorner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:52:15.535661+00:00
-- url     : https://prove2.me/theorems/79de7f7e-c1d2-4c79-8120-d064d593ff35
-- title:
--   Corollary IV.13: For c1h1 source, (H(X|Y),H(Y)) is quantum-Fbar achievable.
-- statement:
--   Consider a finite pure-letter iid multiple source, allowing correlated classical laws and entangled source letters where the model permits them. Quantum rate regions use separate local CPTP encoders and a joint CPTP decoder, with rates converging and the named average half-trace, average-fidelity or entanglement-fidelity error tending to zero. Entanglement fidelity is used only when every sender system is a full matrix algebra. For classical/hybrid senders $X_1,\ldots,X_s,Y$, conditional entropies are evaluated in the computed joint source average, the Y rate is exactly $H(Y)$, and every sender subset, including empty/full, is tested.
--
--   $$
--   (H(X\mid Y),H(Y))\in\mathcal R_{q,\bar F}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 54, Corollary IV.13

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

/-- Corollary IV.13, PDF p.54: correlated classical/hybrid source. -/
theorem classicalQuantumCorner (S : HybridSource 1) :
    S.withYRate (fun _ => S.subsetEntropy Finset.univ) ∈ quantumSourceRegion S.multiple := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
