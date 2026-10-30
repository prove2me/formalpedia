-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_trivial_amplification
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.trivial_amplification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:59:18.081571+00:00
-- url     : https://prove2.me/theorems/b30ef875-9083-438e-a1cc-f7d01b0e0da4
-- title:
--   §II.A.1 Eq.(11): trivial amplification
-- statement:
--   Forward an input qubit, append a maximally mixed qubit, and randomly exchange the output labels. The resulting fixed channel has common single-copy fidelity
--
--   $$
--   F_A(\psi)=F_B(\psi)=\tfrac34\quad\text{for all normalized }\psi.
--   $$
--
--   Random output labels implement the source’s random-particle observation convention.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 7, §II.A.1 Eq.(11): trivial amplification

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.A.1, PDF p.7 Eq.(11): random output labels give BOTH clones fidelity 3/4. -/
theorem trivial_amplification :
    IsBoseInputChannel (shuffleCloner (d := 2) (N := 1) (M := 2) (by omega)) ∧
    UniformCloner (shuffleCloner (d := 2) (N := 1) (M := 2) (by omega)) (3 / 4) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
