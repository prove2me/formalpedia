-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_alpha_family_irreversibility
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.alpha_family_irreversibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:28:08.460677+00:00
-- url     : https://prove2.me/theorems/7d52a40e-c34f-4d36-844f-448a69227d54
-- title:
--   Explicit alpha-family estimates and the strict irreversibility chain
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $21/50\le\alpha\le1/2$, $\psi_1=\sqrt\alpha|01\rangle-\sqrt{1-\alpha}|10\rangle$, $\psi_2=\sqrt\alpha|02\rangle-\sqrt{1-\alpha}|20\rangle$, and $\rho^{(\alpha)}=(|\psi_1\rangle\langle\psi_1|+|\psi_2\rangle\langle\psi_2|)/2$. With $E_W$ the infimum of $\log_2\|X^{T_B}\|_1$ over Hermitian $X\ge\rho$, and $E_\eta$ the support-sandwich lower bound, the explicit estimates are
--
--   $$E_W(\rho^{(\alpha)})\le\log_2\|(\rho^{(\alpha)})^{T_B}\|_1=\log_2(1+\sqrt{2\alpha(1-\alpha)}),\qquad E_\eta(\rho^{(\alpha)})\ge-\log_2(1-\alpha).$$
--
--   Moreover,
--
--   $$\log_2(1+\sqrt{2\alpha(1-\alpha)})<-\log_2(1-\alpha),\qquad E_D(\rho^{(\alpha)})\le E_W(\rho^{(\alpha)})<E_\eta(\rho^{(\alpha)})\le E_C(\rho^{(\alpha)}).$$
--
--   The decimal endpoints are exact rationals. Below $\alpha=1/2$ this family need not be antisymmetric.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 5, Unnumbered family result: explicit irreversibility for 0.42<=alpha<=0.5

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

/-- arXiv:1606.09421v3, PDF pp.4--5: exact rational parameter interval,
both explicit estimates, the trace-norm evaluation, and the full irreversibility chain. -/
theorem alpha_family_irreversibility (alpha : ℝ)
    (hlower : (21/50 : ℝ) ≤ alpha) (hupper : alpha ≤ (1/2 : ℝ)) :
    wangDuanBound (alphaState alpha) ≤ Real.logb 2 (1 + Real.sqrt (2*alpha*(1-alpha))) ∧
    traceNorm (gamma (alphaState alpha)) = 1 + Real.sqrt (2*alpha*(1-alpha)) ∧
    -Real.logb 2 (1-alpha) ≤ etaEntanglement (alphaState alpha) ∧
    Real.logb 2 (1 + Real.sqrt (2*alpha*(1-alpha))) < -Real.logb 2 (1-alpha) ∧
    pptDistillable (alphaState alpha) ≤ (wangDuanBound (alphaState alpha) : EReal) ∧
    wangDuanBound (alphaState alpha) < etaEntanglement (alphaState alpha) ∧
    (etaEntanglement (alphaState alpha) : EReal) ≤ asymptoticEntanglementCost false (alphaState alpha) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
