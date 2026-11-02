-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_rhoV_cost_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.rhoV_cost_relative_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:21:12.610634+00:00
-- url     : https://prove2.me/theorems/7b4e283e-0566-4f46-a3d7-7cc1bceb2382
-- title:
--   One-ebit cost and asymptotic PPT relative entropy of rho_v
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Put $|v_1\rangle=(|01\rangle-|10\rangle)/\sqrt2$, $|v_2\rangle=(|02\rangle-|20\rangle)/\sqrt2$, and $\rho_v=(|v_1\rangle\langle v_1|+|v_2\rangle\langle v_2|)/2$. Let $E_R^\infty$ denote the positive-block regularization of relative entropy to normalized PPT states. Then
--
--   $$E_C(\rho_v)=E_R^\infty(\rho_v)=1.$$
--
--   Both values are exactly one ebit per copy; this statement does not replace PPT operations by LOCC.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 3, Proposition 2: PPT cost and regularized PPT relative entropy of rho_v

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

/-- arXiv:1606.09421v3, PDF pp.3--4, Proposition 2: both printed equalities. -/
theorem rhoV_cost_relative_entropy :
    asymptoticEntanglementCost false rhoV = 1 ∧ regularizedPptRelativeEntropy rhoV = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
