-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_eta_not_tight
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.eta_not_tight
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:30:32.099513+00:00
-- url     : https://prove2.me/theorems/fcedc39e-f23b-41c8-879d-8c64b4030045
-- title:
--   The support lower bound can fall below PPT distillable entanglement
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $P_a$ project onto the three-dimensional antisymmetric subspace of $\mathbb C^3\otimes\mathbb C^3$, and put $\sigma_a=P_a/3=(I-F)/6$, where $F$ swaps the qutrits. Let $E_\eta$ be the support-sandwich bound of Eq. (4). Then
--
--   $$E_\eta(\sigma_a)=\log_2(3/2)<E_D(\sigma_a)=E_C(\sigma_a)=\log_2(5/3).$$
--
--   The new evaluation of $E_\eta$ illustrates failure of tightness. The paper explicitly credits the equal operational values to Ref. [12]. This rank-three state is distinct from the rank-two class in the main result.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 5, Discussion unnumbered example: E_eta can be below PPT distillable entanglement

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

/-- arXiv:1606.09421v3, PDF p.5, Discussion: the rank-three example.
The new E_eta evaluation is separated in provenance from the operational
value log2(5/3), which this paragraph explicitly credits to Ref.[12]. -/
theorem eta_not_tight :
    etaEntanglement antisymmetricQutrit = Real.logb 2 (3/2 : ℝ) ∧
    (etaEntanglement antisymmetricQutrit : EReal) < pptDistillable antisymmetricQutrit ∧
    pptDistillable antisymmetricQutrit = (Real.logb 2 (5/3 : ℝ) : EReal) ∧
    asymptoticEntanglementCost false antisymmetricQutrit = (Real.logb 2 (5/3 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
