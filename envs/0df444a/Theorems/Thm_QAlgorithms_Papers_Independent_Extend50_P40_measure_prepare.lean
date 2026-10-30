-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_measure_prepare
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.measure_prepare
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:57:47.015085+00:00
-- url     : https://prove2.me/theorems/b89c20eb-340c-440a-809f-19d7c44c0068
-- title:
--   §II.A.1 Eq.(10): random-basis measure-and-prepare cloning
-- statement:
--   Measure a qubit in a uniformly random basis and prepare two copies of the observed eigenstate. Uniform means normalized spherical probability measure, $d\varphi\,dz/(4\pi)$ with $z\in[-1,1]$. This fixed channel has, for every normalized input $\psi$,
--
--   $$
--   \langle\psi|\rho_A|\psi\rangle=\langle\psi|\rho_B|\psi\rangle=\tfrac23.
--   $$
--
--   The fidelity is independent of the input and refers to each labeled single clone.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 7, §II.A.1 Eq.(10): random-basis measure-and-prepare cloning

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

/-- II.A.1, PDF p.7 Eq.(10): uniform random measurement basis gives fidelity 2/3. -/
theorem measure_prepare :
    IsChannel randomBasisCloner ∧ ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      pureFidelity psi (traceRight (randomBasisCloner (pureDensity psi))) = 2 / 3 ∧
      pureFidelity psi (traceLeft (randomBasisCloner (pureDensity psi))) = 2 / 3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
