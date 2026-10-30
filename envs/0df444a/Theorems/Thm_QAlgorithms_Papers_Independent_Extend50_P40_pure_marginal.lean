-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_pure_marginal
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.pure_marginal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:26:17.135997+00:00
-- url     : https://prove2.me/theorems/e02fc4fd-5456-449d-8171-9ebc470383c6
-- title:
--   Appendix A after Eq.(A11): a pure marginal forces a product
-- statement:
--   Let $\rho_{AB}$ be a positive trace-one two-qubit density with $\operatorname{Tr}_B\rho_{AB}=|\psi\rangle\langle\psi|$ for a normalized vector $\psi$. Then
--
--   $$
--   \rho_{AB}=|\psi\rangle\langle\psi|\otimes\operatorname{Tr}_A\rho_{AB}.
--   $$
--
--   Consequently every Pauli correlation coefficient factors as the product of the corresponding pure Bloch coordinate of A and Bloch coordinate of the actual marginal of B.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 31, Appendix A after Eq.(A11): a pure marginal forces a product

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

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- Appendix A, PDF p.31 after Eq.(A11): a pure marginal forces a product,
with the other factor the actual opposite partial trace. -/
theorem pure_marginal (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : ‖psi‖ = 1) (hA : traceRight rho = pureDensity psi) :
    rho = Matrix.kronecker (pureDensity psi) (traceLeft rho) ∧
    ∀ i j : Fin 3, (rho * Matrix.kronecker (sigma i) (sigma j)).trace.re =
      vectorBloch psi i * densityBloch (traceLeft rho) j := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
