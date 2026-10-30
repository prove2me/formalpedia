-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_tight_nosignaling_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.tight_nosignaling_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:56:12.109421+00:00
-- url     : https://prove2.me/theorems/d8bfd27f-e36a-4a75-819f-38ba1302dd52
-- title:
--   §I.E.1: tight no-signaling bound for qubit symmetric universal cloning
-- statement:
--   Consider any family of positive trace-one two-qubit outputs on pure inputs, with both marginals $\eta|\psi\rangle\langle\psi|+(1-\eta)I/2$, full identical-unitary covariance (9), and equal average outputs for the $x$ and $z$ eigenstate ensembles. Then
--
--   $$
--   \eta\le\tfrac23,\qquad F=(1+\eta)/2\le\tfrac56.
--   $$
--
--   A genuine fixed CPTP channel attains equality and satisfies all the stated family conditions. Necessity is proved in the larger no-signaling family model, not only for channels.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 6, §I.E.1: tight no-signaling bound for qubit symmetric universal cloning

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

/-- I.E.1, PDF p.6: tight no-signaling bound in the explicitly covariant model (9).
The family bound does not assume complete positivity; attainment is a genuine channel. -/
theorem tight_nosignaling_bound :
    (∀ (F : Superop (Fin 2) (Fin 2 × Fin 2)) (eta : ℝ), NoSignalingFamily F eta →
      eta ≤ 2 / 3 ∧ (1 + eta) / 2 ≤ 5 / 6) ∧
    ∃ T : Superop (Fin 2) (Fin 2 × Fin 2), IsChannel T ∧ NoSignalingFamily T (2 / 3) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
