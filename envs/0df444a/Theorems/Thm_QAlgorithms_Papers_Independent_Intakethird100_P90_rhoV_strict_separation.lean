-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_rhoV_strict_separation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.rhoV_strict_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:24:24.733443+00:00
-- url     : https://prove2.me/theorems/cf972121-d523-4797-a304-0bd364f45db4
-- title:
--   Strict separation between regularized Rains and PPT relative entropy
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho_v$ be the equal mixture of the unit antisymmetric kets $(|01\rangle-|10\rangle)/\sqrt2$ and $(|02\rangle-|20\rangle)/\sqrt2$. Let $R^\infty$ be the positive-block regularization of the Rains bound and $E_R^\infty$ that of relative entropy to normalized PPT states. Then
--
--   $$E_D(\rho_v)=R^\infty(\rho_v)<E_R^\infty(\rho_v)=E_C(\rho_v).$$
--
--   This is the full equality/strict-inequality/equality chain announced as the main contribution in Eq. (3).
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 2, Unnumbered main result, Eq.(3): strict regularized Rains/relative-entropy separation

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

/-- arXiv:1606.09421v3, PDF p.2, Eq.(3): preserve the full strict chain. -/
theorem rhoV_strict_separation :
    pptDistillable rhoV = regularizedRains rhoV ∧
    regularizedRains rhoV < regularizedPptRelativeEntropy rhoV ∧
    regularizedPptRelativeEntropy rhoV = asymptoticEntanglementCost false rhoV := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
