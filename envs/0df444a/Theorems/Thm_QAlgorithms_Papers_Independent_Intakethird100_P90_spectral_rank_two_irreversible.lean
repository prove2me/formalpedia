-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_spectral_rank_two_irreversible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.spectral_rank_two_irreversible
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:23:37.589218+00:00
-- url     : https://prove2.me/theorems/161554e9-567d-4822-b85c-97ad93a8b069
-- title:
--   Irreversibility in the complex spectral parametrization
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $0<p<1$, $u_1=(|01\rangle-|10\rangle)/\sqrt2$, and $u_2=(|a\rangle\otimes|b\rangle-|b\rangle\otimes|a\rangle)/\sqrt2$ for complex qutrit vectors $a,b$. Assume $u_2$ is a unit vector orthogonal to $u_1$, so that the displayed expression is a spectral decomposition of the state
--
--   $$\rho=p|u_1\rangle\langle u_1|+(1-p)|u_2\rangle\langle u_2|.$$
--
--   Then
--
--   $$E_D(\rho)<1=E_C(\rho).$$
--
--   Orthogonality is required also at $p=1/2$. The statement retains arbitrary complex spectral data rather than restricting to the real-angle representative used after a local basis change.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 7, Proposition 5: spectral form of the rank-two antisymmetric example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P90

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P90

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropy rains target canonicalMatrix allowed pptDistillable)

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies IsPPT)

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Gap48.P32 (antisymmetricQutrit)

/-- arXiv:1606.09421v3, PDF pp.4,7, Eq.(11) and Proposition 5. The spectral
vectors are unit and orthogonal, also when p=1/2; a,b may be complex. -/
theorem spectral_rank_two_irreversible
    (rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (p : ℝ) (a b : EuclideanSpace ℂ (Fin 3))
    (hstate : IsDensityMatrix rho) (hp0 : 0 < p) (hp1 : p < 1)
    (hunit : ‖exteriorKet a b‖ = 1)
    (horth : inner ℂ (antisymmetricKet 1) (exteriorKet a b) = 0)
    (hspectral : rho = (p : ℂ) • pureDensity (antisymmetricKet 1) +
      ((1-p : ℝ) : ℂ) • pureDensity (exteriorKet a b)) :
    pptDistillable rho < 1 ∧ asymptoticEntanglementCost false rho = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
