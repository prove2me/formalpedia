-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_eta_tensor_additivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.eta_tensor_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:22:55.05321+00:00
-- url     : https://prove2.me/theorems/eeb25876-337c-4525-aec7-6a96896b03b9
-- title:
--   Tensor additivity of the support bound
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho_1$ on $A\otimes B$ and $\rho_2$ on $A'\otimes B'$ be arbitrary normalized states, with independently chosen local dimensions. For a state $\rho$ with support projection $P$, define $E_\eta(\rho)=-\log_2\min\{\|Y^{T_B}\|_\infty:Y=Y^\dagger,\ -Y\le P^{T_B}\le Y\}$. Across the product bipartition $AA':BB'$,
--
--   $$E_\eta(\rho_1\otimes\rho_2)=E_\eta(\rho_1)+E_\eta(\rho_2).$$
--
--   The product partial transpose acts on both $B$ and $B'$. This is the additivity needed to retain the support lower bound in the asymptotic regime.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 6, Proposition 4: tensor additivity of E_eta

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

/-- arXiv:1606.09421v3, PDF pp.3,6, Proposition 4: independent local dimensions
and a product bipartition AA':BB', with both Bob factors transposed. -/
theorem eta_tensor_additivity {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    etaEntanglement (regroupProduct rho sigma) =
      etaEntanglement rho + etaEntanglement sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
