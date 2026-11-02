-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_deterministicSupportInvariance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.deterministicSupportInvariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:16:20.487193+00:00
-- url     : https://prove2.me/theorems/607b4a5f-de3d-4860-84d5-9453b664e046
-- title:
--   Deterministic entanglement depends only on support
-- statement:
--   Let $\rho,\sigma$ be normalized states on the same arbitrary finite nonzero bipartite spaces with $\operatorname{supp}\rho=\operatorname{supp}\sigma$. Let $E_1$ be the one-copy exact positive-real-target PPT rate, and let $E_{\Gamma,0}(\rho)=\sup_{n\ge1}E_1(\rho^{\otimes n})/n$. Then
--
--   $$E_1(\rho)=E_1(\sigma),\qquad E_{\Gamma,0}(\rho)=E_{\Gamma,0}(\sigma).$$
--
--   Equal supports persist under tensor powers. The invariance applies to these exact deterministic quantities; no full-support assumption is imposed.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 4, Unnumbered main result: deterministic entanglement depends only on support

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Support dependence announced on PDF p.4 and established by (15) on p.5.
Both one-copy and regularized deterministic values are invariant; no full-rank
assumption and no invariance of E_Gamma or E_W is asserted. -/
theorem deterministicSupportInvariance [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : supportSpace rho = supportSpace sigma) :
    oneCopyExact rho = oneCopyExact sigma ∧ exactRegularized rho = exactRegularized sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
