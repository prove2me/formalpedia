-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_bloch_representation
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.bloch_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:24:37.848074+00:00
-- url     : https://prove2.me/theorems/8d2806d5-cb0b-495b-8420-e1e4bb35a988
-- title:
--   Appendix A Eqs.(A1)–(A5),(A10)–(A11): Bloch representation
-- statement:
--   For standard Pauli matrices X,Y,Z with $Y_{01}=-i$, every qubit density has a real Bloch vector $m$, and conversely every vector in the unit ball defines a density. For a normalized $\psi=(\alpha,\beta)$,
--
--   $$
--   \rho=\tfrac12(I+m\cdot\sigma),\quad\|m\|\le1,\qquad m_\psi=(2\Re(\overline\alpha\beta),2\Im(\overline\alpha\beta),|\alpha|^2-|\beta|^2).
--   $$
--
--   The unit boundary is exactly the pure densities; spherical coordinates parametrize their rays. The theorem also gives Pauli relations and the full two-qubit correlation expansion with its actual partial traces. The printed y sign is corrected; mixed Bloch vectors need not be unit.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 30, Appendix A Eqs.(A1)–(A5),(A10)–(A11): Bloch representation

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

/-- Appendix A, PDF pp.30–31 Eqs.(A1)–(A5),(A10)–(A11): Bloch ball, pure
boundary, and all two-qubit correlation coefficients. Printed +2 Im(alpha beta*)
is corrected to -2 Im(alpha beta*) by the source's own standard Pauli Y. -/
theorem bloch_representation :
    (∀ k : Fin 3, sigma k * sigma k = 1 ∧ (sigma k).trace = 0) ∧
    sigma 0 * sigma 1 = Complex.I • sigma 2 ∧
    sigma 1 * sigma 2 = Complex.I • sigma 0 ∧
    sigma 2 * sigma 0 = Complex.I • sigma 1 ∧
    (∀ i j : Fin 3, i ≠ j → sigma i * sigma j = -(sigma j * sigma i)) ∧
    (∀ m : Fin 3 → ℝ, (∑ k, m k ^ 2) ≤ 1 →
      IsDensityMatrix (finBlochDensity m) ∧ densityBloch (finBlochDensity m) = m) ∧
    (∀ theta azimuth : ℝ, ‖spherical theta azimuth‖ = 1 ∧
      vectorBloch (spherical theta azimuth) =
        ![Real.sin theta * Real.cos azimuth, Real.sin theta * Real.sin azimuth, Real.cos theta]) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → ∃ theta ∈ Set.Icc (0 : ℝ) Real.pi,
      ∃ azimuth ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        pureDensity psi = pureDensity (spherical theta azimuth)) ∧
    (∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix rho →
      rho = finBlochDensity (densityBloch rho) ∧ ∑ k, densityBloch rho k ^ 2 ≤ 1 ∧
      ((∑ k, densityBloch rho k ^ 2) = 1 ↔ ∃ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 ∧ rho = pureDensity psi)) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      densityBloch (pureDensity psi) = vectorBloch psi ∧ pureDensity psi = finBlochDensity (vectorBloch psi)) ∧
    (∀ rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsDensityMatrix rho →
      rho = (1 / 4 : ℂ) •
        (1 + Matrix.kronecker (∑ i, (densityBloch (traceRight rho) i : ℂ) • sigma i) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (∑ j, (densityBloch (traceLeft rho) j : ℂ) • sigma j) +
          ∑ i : Fin 3, ∑ j : Fin 3,
            (((rho * Matrix.kronecker (sigma i) (sigma j)).trace.re : ℝ) : ℂ) •
              Matrix.kronecker (sigma i) (sigma j)) ∧
      traceRight rho = finBlochDensity (densityBloch (traceRight rho)) ∧
      traceLeft rho = finBlochDensity (densityBloch (traceLeft rho))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
