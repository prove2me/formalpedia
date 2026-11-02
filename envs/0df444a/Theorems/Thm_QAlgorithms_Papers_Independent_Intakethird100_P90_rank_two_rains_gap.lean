-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_rank_two_rains_gap
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.rank_two_rains_gap
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:25:31.022308+00:00
-- url     : https://prove2.me/theorems/2153e6ec-429a-4dd7-9783-cfc2a49bf04f
-- title:
--   Both Rains bounds lie below asymptotic PPT relative entropy
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho$ be any rank-two state supported on the two-qutrit antisymmetric subspace. Let $R(\rho)=\inf\{S(\rho\Vert\sigma):\sigma\ge0,\ \|\sigma^{T_B}\|_1\le1\}$, $R^\infty(\rho)=\inf_{n\ge1}R(\rho^{\otimes n})/n$, and let $E_R^\infty$ be the corresponding regularization of relative entropy to normalized PPT states. Then
--
--   $$R(\rho)<E_R^\infty(\rho),\qquad R^\infty(\rho)<E_R^\infty(\rho).$$
--
--   The abstract's byproduct concerns both the single-copy bound and its regularization throughout the rank-two class.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 1, Abstract byproduct: both Rains quantities lie strictly below asymptotic PPT relative entropy

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

/-- arXiv:1606.09421v3, PDF pp.1--2,4--5,7: the abstract includes both
single-copy and regularized Rains quantities for every rank-two state in the class. -/
theorem rank_two_rains_gap
    (rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hstate : IsDensityMatrix rho) (hrank : stateRank rho = 2)
    (hsupport : antisymmetricSupported rho) :
    rains rho < regularizedPptRelativeEntropy rho ∧
    regularizedRains rho < regularizedPptRelativeEntropy rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
