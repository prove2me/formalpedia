-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_deterministicRegularization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.deterministicRegularization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:17:13.818582+00:00
-- url     : https://prove2.me/theorems/16ab3c8f-d927-4063-ba2e-a4d25336ddf4
-- title:
--   The regularized exact rate is an asymptotic limit
-- statement:
--   Let $\rho$ be any normalized finite-dimensional bipartite state. Define $E_1(\rho)$ independently as the supremum of $\log_2 k$ over real $k>0$ with $F_\Gamma(\rho,k)=1$, and define $E_{\Gamma,0}(\rho)$ by the supremum of positive-blocklength ratios. Then
--
--   $$\lim_{n\to\infty,\ n\ge1}\frac{E_1(\rho^{\otimes n})}{n}=E_{\Gamma,0}(\rho):=\sup_{n\ge1}\frac{E_1(\rho^{\otimes n})}{n}.$$
--
--   The limit is through positive integers and is finite. This is a regularization statement and does not assert additivity of the one-copy rate.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 4, Unnumbered result: regularization equals the asymptotic limit

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

/-- The asymptotic formula on PDF p.4. The printed subscript "lim_{n>=1}"
is interpreted as n tending to infinity through positive blocklengths;
exactRegularized is independently defined by a supremum, not by this limit. -/
theorem deterministicRegularization [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    Tendsto (fun n : ℕ => oneCopyExact (regroupedPower rho (n+1)) / (n+1 : ℝ))
      atTop (nhds (exactRegularized rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
