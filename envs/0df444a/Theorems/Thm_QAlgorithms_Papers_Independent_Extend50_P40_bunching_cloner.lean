-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_bunching_cloner
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.bunching_cloner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:22:24.157379+00:00
-- url     : https://prove2.me/theorems/4edbed87-69c3-4ffa-8d07-79133dbfed60
-- title:
--   §VI.A.1 Eq.(101): symmetric projection via photon bunching
-- statement:
--   Combine the input photon with one member of a singlet pair and condition on their symmetric projection $S_2=I-|\Psi^-\rangle\langle\Psi^-|$. For every normalized input, the bunching event has probability 3/4 and
--
--   $$
--   \rho_{AB\mid\rm bunch}=\frac43 S_2\bigl(|\psi\rangle\langle\psi|\otimes I/2\bigr)S_2,\qquad F_A=F_B=\tfrac56.
--   $$
--
--   The full selected three-photon amplitude equals the Buzek–Hillery output and gives anti-clone fidelity 2/3. The unnormalized operation is a trace-decreasing instrument branch, not a TP projection.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 26, §VI.A.1 Eq.(101): symmetric projection via photon bunching

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

/-- VI.A.1, PDF pp.25–26 Eq.(101): positive-probability bunching conditioning,
not an unconditioned TP projection. The resulting cloner and anti-clone are exact. -/
theorem bunching_cloner (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : ‖psi‖ = 1) :
    ‖bunchingVector psi‖ ^ 2 = 3 / 4 ∧
    ((Real.sqrt (3 / 4) : ℂ)⁻¹) • bunchingVector psi = bhOutput psi ∧
    pureFidelity (orthogonalQubit psi)
      (marginalMachine (((Real.sqrt (3 / 4) : ℂ)⁻¹) • bunchingVector psi)) = 2 / 3 ∧
    symmetricPairᴴ = symmetricPair ∧ symmetricPair * symmetricPair = symmetricPair ∧
    (bunching (pureDensity psi)).trace = (3 / 4 : ℂ) ∧
    let rho := (4 / 3 : ℂ) • bunching (pureDensity psi)
    IsDensityMatrix rho ∧ rho = cloneChannel bhMatrix (pureDensity psi) ∧
      pureFidelity psi (traceRight rho) = 5 / 6 ∧ pureFidelity psi (traceLeft rho) = 5 / 6 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
