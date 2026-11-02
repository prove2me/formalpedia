-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_eta_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.eta_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:20:33.672772+00:00
-- url     : https://prove2.me/theorems/b545da90-3bef-4748-b5ce-341e767e2a65
-- title:
--   The additive support bound lower-bounds PPT relative entropy and cost
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho$ be any bipartite state, and let $P$ be its support projection. Define
--
--   $$\eta(\rho)=\min_{Y=Y^\dagger,\,-Y\le P^{T_B}\le Y}\|Y^{T_B}\|_\infty,\qquad E_\eta(\rho)=-\log_2\eta(\rho).$$
--
--   Let $E_R(\rho)=\inf_{\sigma\in\Gamma}S(\rho\Vert\sigma)$, where $\Gamma$ is the set of normalized PPT states, and $E_R^\infty(\rho)=\inf_{n\ge1}E_R(\rho^{\otimes n})/n$. Relative entropy is $+\infty$ when support inclusion fails. Then
--
--   $$E_R^\infty(\rho)\ge E_\eta(\rho),\qquad E_{C,\mathrm{LOCC}}(\rho)\ge E_C(\rho)\ge E_\eta(\rho).$$
--
--   This provides a support-dependent lower bound for both operational formation costs, including singular states.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 3, Proposition 1: additive support bound below regularized PPT relative entropy and cost

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

/-- arXiv:1606.09421v3, PDF p.3, Proposition 1, including the complete cost consequence. -/
theorem eta_lower_bound {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hstate : IsDensityMatrix rho) :
    (etaEntanglement rho : EReal) ≤ regularizedPptRelativeEntropy rho ∧
    asymptoticEntanglementCost false rho ≤ asymptoticEntanglementCost true rho ∧
    (etaEntanglement rho : EReal) ≤ asymptoticEntanglementCost false rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
