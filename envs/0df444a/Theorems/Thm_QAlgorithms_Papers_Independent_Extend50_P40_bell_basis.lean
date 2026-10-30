-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_bell_basis
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.bell_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:25:32.749025+00:00
-- url     : https://prove2.me/theorems/480688a5-fc61-42e9-bde7-165703e88f4f
-- title:
--   Appendix A Eqs.(A6)–(A9): Bell basis and singlet invariance
-- statement:
--   The four normalized Bell states $\Phi^\pm=(|00\rangle\pm|11\rangle)/\sqrt2$ and $\Psi^\pm=(|01\rangle\pm|10\rangle)/\sqrt2$ form a complete orthonormal basis. For every one-qubit unitary U,
--
--   $$
--   (U\otimes U)|\Psi^-\rangle=\det(U)|\Psi^-\rangle.
--   $$
--
--   In particular the singlet density is invariant under U⊗U. The determinant phase is retained, avoiding the false claim of literal vector invariance under all U(2).
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 30, Appendix A Eqs.(A6)–(A9): Bell basis and singlet invariance

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

/-- Appendix A, PDF p.30 Eqs.(A6)–(A9): orthonormal complete Bell basis and
singlet invariance as a density/ray under U(2), retaining its determinant phase. -/
theorem bell_basis :
    (∀ k l : Fin 4, inner ℂ (bellBasisState k) (bellBasisState l) = if k = l then 1 else 0) ∧
    (∑ k : Fin 4, pureDensity (bellBasisState k)) = 1 ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      WithLp.toLp 2 ((Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)).mulVec (bellBasisState 3)) =
        Matrix.det (U : Matrix (Fin 2) (Fin 2) ℂ) • bellBasisState 3 ∧
      Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) * pureDensity (bellBasisState 3) *
        (Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = pureDensity (bellBasisState 3)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
