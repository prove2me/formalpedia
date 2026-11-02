-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_ppt_support_weak_duality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.ppt_support_weak_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:29:35.522134+00:00
-- url     : https://prove2.me/theorems/9b79440b-d0b3-4f97-a89c-ea31e8228e29
-- title:
--   PPT support-overlap weak duality with one-sided constraints
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho$ be a bipartite state, $P$ its support projection, and $\Gamma$ the normalized PPT states. Define the two optimization values independently. Then
--
--   $$\max_{\sigma\in\Gamma}\operatorname{Tr}(P\sigma)\le\min\{t:\exists Y=Y^\dagger,\ P^{T_B}\le Y,\ Y^{T_B}\le tI\}.$$
--
--   The maximum and minimum are attained. The dual has only the displayed one-sided inequalities. The result asserts weak duality and does not identify the values by an additional equality.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 7, Supplemental unnumbered result, Eq.(16): PPT-support overlap weak duality

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

/-- arXiv:1606.09421v3, PDF p.7, Eq.(16): weak duality with exactly the
two ONE-SIDED constraints. The source's maximum and minimum are attained;
no equality of these independently defined values is claimed here. -/
theorem ppt_support_weak_duality {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hstate : IsDensityMatrix rho) :
    supportOverlap rho ≤ supportDual rho ∧
    (∃ sigma : Matrix (A × B) (A × B) ℂ, IsPPT sigma ∧
      (supportProjection rho * sigma).trace.re = supportOverlap rho) ∧
    (∃ Y, supportDualFeasible rho (supportDual rho) Y) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
