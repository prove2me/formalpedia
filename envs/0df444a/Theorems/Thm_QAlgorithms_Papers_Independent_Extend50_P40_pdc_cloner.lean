-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_pdc_cloner
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.pdc_cloner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:21:40.982769+00:00
-- url     : https://prove2.me/theorems/992c479d-58c7-4fdf-9663-dc0f2b32b9bc
-- title:
--   §VI.A.1 Eqs.(97)–(100): first-order PDC realizes the optimal cloner
-- statement:
--   In the ideal selected first-order sector of the polarization-matched PDC Hamiltonian (97), construct the normalized singlet-pair creation amplitude for an arbitrary normalized input photon $\psi$. It equals the corrected Buzek–Hillery amplitude and has
--
--   $$
--   F_A=F_B=\tfrac56,\qquad F_{\rm anti}=\tfrac23.
--   $$
--
--   The source’s identical SU(2) polarization covariance is exact. The claim is about the selected first-order sector with indistinguishable wave packets; no finite-gain deterministic success probability or unrestricted U(2) vector invariance is asserted.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 25, §VI.A.1 Eqs.(97)–(100): first-order PDC realizes the optimal cloner

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

/-- VI.A.1, PDF p.25 Eqs.(97)–(100): ideal selected first-order PDC amplitude.
The symmetric two-signal-photon coordinate is (|01>+|10>)/sqrt(2), so the
corrected BH isometry is precisely the first-order emission map, in any polarization. -/
theorem pdc_cloner :
    (∀ psi : EuclideanSpace ℂ (Fin 2), pdcFirstOrder psi = bhOutput psi) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      ‖bhOutput psi‖ = 1 ∧ pureFidelity psi (cloneMarginalA (bhOutput psi)) = 5 / 6 ∧
      pureFidelity psi (cloneMarginalB (bhOutput psi)) = 5 / 6 ∧
      pureFidelity (orthogonalQubit psi) (marginalMachine (bhOutput psi)) = 2 / 3) ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ, Matrix.det (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)) * bhMatrix =
        bhMatrix * (U : Matrix (Fin 2) (Fin 2) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
