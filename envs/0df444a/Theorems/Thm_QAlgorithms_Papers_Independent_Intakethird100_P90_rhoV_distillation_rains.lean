-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_rhoV_distillation_rains
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.rhoV_distillation_rains
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:22:02.582209+00:00
-- url     : https://prove2.me/theorems/879eaada-4c76-4622-90d8-eaded1a502cd
-- title:
--   Exact PPT yield and regularized Rains value of rho_v
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho_v$ be the equal mixture of $(|01\rangle-|10\rangle)/\sqrt2$ and $(|02\rangle-|20\rangle)/\sqrt2$. Define $R(\rho)=\inf\{S(\rho\Vert\sigma):\sigma\ge0,\ \|\sigma^{T_B}\|_1\le1\}$ and $R^\infty(\rho)=\inf_{n\ge1}R(\rho^{\otimes n})/n$. Then
--
--   $$E_D(\rho_v)=R^\infty(\rho_v)=\log_2(1+1/\sqrt2).$$
--
--   The operational yield is strictly below one ebit. No identification of the continuous one-copy SDP with an unrounded integer Bell rank is used.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 4, Proposition 3: PPT distillable entanglement and regularized Rains value of rho_v

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

/-- arXiv:1606.09421v3, PDF p.4, Proposition 3, Eq.(7): both quantitative equalities. -/
theorem rhoV_distillation_rains :
    pptDistillable rhoV = (Real.logb 2 (1 + 1 / Real.sqrt 2) : EReal) ∧
    regularizedRains rhoV = (Real.logb 2 (1 + 1 / Real.sqrt 2) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
