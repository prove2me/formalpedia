-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_wang_duan_irreversibility_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.wang_duan_irreversibility_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:26:21.537889+00:00
-- url     : https://prove2.me/theorems/b4e62721-a4aa-4976-b9c1-8532ec1e9d49
-- title:
--   An E_W/E_eta gap guarantees PPT and LOCC irreversibility
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   For a bipartite state $\rho$ with support projection $P$, put $E_W(\rho)=\inf_{X=X^\dagger,\,X\ge\rho}\log_2\|X^{T_B}\|_1$ and $E_\eta(\rho)=-\log_2\min\{\|Y^{T_B}\|_\infty:Y=Y^\dagger,\ -Y\le P^{T_B}\le Y\}$. If $E_W(\rho)<E_\eta(\rho)$, then
--
--   $$E_D(\rho)<E_C(\rho),\qquad E_{D,\mathrm{LOCC}}(\rho)<E_{C,\mathrm{LOCC}}(\rho).$$
--
--   The paper credits the background upper bound $E_D\le E_W$ to Ref. [30]. The additional LOCC conclusion is explicitly advertised in the abstract and discussion.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 4, Unnumbered sufficient condition: E_W below E_eta forces irreversibility

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

/-- arXiv:1606.09421v3, PDF pp.4--5: the displayed PPT criterion and its
explicitly advertised LOCC consequence. E_D<=E_W is credited to Ref.[30]. -/
theorem wang_duan_irreversibility_criterion {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hstate : IsDensityMatrix rho)
    (hgap : wangDuanBound rho < etaEntanglement rho) :
    pptDistillable rho < asymptoticEntanglementCost false rho ∧
    loccDistillable rho < asymptoticEntanglementCost true rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
