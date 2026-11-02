-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_eta_sdp_duality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.eta_sdp_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:28:49.859419+00:00
-- url     : https://prove2.me/theorems/b99b3792-f251-4265-a873-529731582967
-- title:
--   Attained independent primal and dual descriptions of eta
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho$ be a bipartite state and $P$ its support projection. Define the primal and dual independently by
--
--   $$\eta_p=\inf\{t:\exists Y=Y^\dagger,\ -Y\le P^{T_B}\le Y,\ -tI\le Y^{T_B}\le tI\},$$
--
--   $$\eta_d=\sup\{\operatorname{Tr}P(V-F)^{T_B}:V,F,W,X\ge0,\ V+F\le(W-X)^{T_B},\ \operatorname{Tr}(W+X)\le1\}.$$
--
--   Both extrema are attained, and
--
--   $$0<\eta(\rho)=\eta_p=\eta_d,\qquad E_\eta(\rho)=-\log_2\eta_p,$$
--
--   where $\eta(\rho)$ is the minimum of $\|Y^{T_B}\|_\infty$ over the support sandwich in Eq. (4). These finite SDPs specify the paper's computable lower bound; no exact real-input bit-complexity claim is added.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 6, Supplemental unnumbered result, Eqs.(12)–(13): attained primal/dual description of eta

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

/-- arXiv:1606.09421v3, PDF p.6, Eqs.(12)--(13): independently defined
primal and dual optima coincide and are attained, and E_eta=-log2 supportEta.
Strict positivity prevents a default logarithm value at zero. -/
theorem eta_sdp_duality {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hstate : IsDensityMatrix rho) :
    0 < supportEta rho ∧ etaPrimal rho = supportEta rho ∧ etaDual rho = etaPrimal rho ∧
    (∃ Y, etaPrimalFeasible rho (etaPrimal rho) Y) ∧
    (∃ V F W X : Matrix (A × B) (A × B) ℂ,
      etaDualFeasible V F W X ∧ etaDualObjective rho V F = etaDual rho) ∧
    etaEntanglement rho = -Real.logb 2 (etaPrimal rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
