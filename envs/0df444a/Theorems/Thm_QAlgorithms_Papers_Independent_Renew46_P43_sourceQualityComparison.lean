-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_sourceQualityComparison
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.sourceQualityComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:15:21.800005+00:00
-- url     : https://prove2.me/theorems/14bbf287-c8dd-4d33-a62a-513dc61a771c
-- title:
--   Theorem I.1: Dbar²≤1−Fbar≤Dbar; for quantum encoders also 1−Fbar≤1−Fe.
-- statement:
--   Let a finite pure-state ensemble on a nonzero finite-dimensional Hilbert space generate iid words, and let a positive-length compression code have arbitrary state-valued encoding and a CPTP decoder. Write bar F for mean word overlap and bar D for mean half trace norm. For a quantum encoder, F_e is the purification overlap of its CPTP extension.
--
--   $$
--   \bar D^2\le 1-\bar F\le\bar D,\qquad 1-\bar F\le 1-F_e\quad\text{for quantum encoders}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 8, Theorem I.1

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

/-- Theorem I.1, PDF p.8. The first chain holds for every arbitrary encoder;
the entanglement-fidelity clause uses each actual quantum extension separately. -/
theorem sourceQualityComparison {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n) :
    c.distortion^2 ≤ 1 - c.fidelity ∧ 1 - c.fidelity ≤ c.distortion ∧
    ∀ E, EncoderExtension c E →
      1 - c.fidelity ≤ 1 - sourceFe (copies n S.average) (c.decode ∘ E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
