-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_rank_two_antisymmetric_irreversible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.rank_two_antisymmetric_irreversible
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:19:32.281242+00:00
-- url     : https://prove2.me/theorems/8c111c88-ce0e-43c9-b8e5-9f6b39d3bc4f
-- title:
--   Every rank-two two-qutrit antisymmetric state is PPT-irreversible
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho$ be any state on $\mathbb C^3\otimes\mathbb C^3$ whose operator range has dimension exactly two and lies in the antisymmetric subspace. Then
--
--   $$E_D(\rho)<1,\qquad E_C(\rho)=1.$$
--
--   Thus every mixed rank-two state in this subspace has a strict asymptotic Bell-pair yield/cost gap. Pure endpoints are excluded by the rank hypothesis.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 1, Abstract: irreversibility for every rank-two two-qutrit antisymmetric state

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

/-- arXiv:1606.09421v3, PDF pp.1--2,4,7: every rank-two two-qutrit
antisymmetric density state has PPT yield strictly below its one-ebit cost. -/
theorem rank_two_antisymmetric_irreversible
    (rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hstate : IsDensityMatrix rho) (hrank : stateRank rho = 2)
    (hsupport : antisymmetricSupported rho) :
    pptDistillable rho < 1 ∧ asymptoticEntanglementCost false rho = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
