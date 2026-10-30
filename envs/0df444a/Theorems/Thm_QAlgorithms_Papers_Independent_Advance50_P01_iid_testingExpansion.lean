-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_iid_testingExpansion
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.iid_testingExpansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:05:03.069992+00:00
-- url     : https://prove2.me/theorems/7e7ad090-f920-43bd-bbee-10983061ca41
-- title:
--   Two-sided iid testing expansion on the full support domain
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   Fix $0<\varepsilon<1$, let $\beta_n^*(\varepsilon)=\min_{\alpha_n(A)\le\varepsilon}\beta_n(A)$, and put $D_H^\varepsilon(\rho^{\otimes n}\Vert\sigma^{\otimes n})=-\log\beta_n^*(\varepsilon)$, without division by $1-\varepsilon$. Then there is a real sequence $r_n=O(\log n)$ such that for all sufficiently large $n$,
--
--   $$D_H^\varepsilon(\rho^{\otimes n}\Vert\sigma^{\otimes n})=nD+\sqrt n\sqrt V\,\Phi^{-1}(\varepsilon)+r_n,\qquad c_-\le r_n\le2\log n+c_+.$$
--
--   The constants $c_-,c_+$ and the threshold may depend on the fixed states and tolerance. The statement includes $V=0$, singular $\rho$, and $\rho=\sigma$, and does not require $\sigma$ to be invertible on the original ambient space. This supplies the two-sided support-complete iid interface.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 3, Introduction: finite-sample expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P01

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Advance50.P01

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile tensorPower)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

attribute [local instance] Classical.propDecidable

-- Match the universe-zero matrix indices of the pinned accepted interfaces.

variable {I : Type} [Fintype I] [DecidableEq I]

-- SupportIncluded is opened directly from the accepted Information100.P71 module.

/-- Main iid expansion announced on source PDF p. 3 and proved on pp. 14–17.
The full support-included domain includes singular rho and V=0; no ambient full-rank
assumption is imposed. The unnormalized testing divergence has a real remainder O(log n),
bounded below by a constant and above by 2 log n plus a constant. Constants may depend
on the fixed states and epsilon. -/
theorem iid_testingExpansion [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma) (epsilon : ℝ)
    (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    ∃ remainder : ℕ → ℝ,
      (remainder =O[atTop] (fun n : ℕ => Real.log (n : ℝ))) ∧
      ∃ lowerConstant upperConstant : ℝ, ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
        iidTestingDivergenceNats rho sigma n epsilon =
          ((secondOrderCenter rho sigma epsilon n + remainder n : ℝ) : EReal) ∧
        lowerConstant ≤ remainder n ∧ remainder n ≤ 2 * Real.log n + upperConstant := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
