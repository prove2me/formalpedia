-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_zeroVariance_characterization
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.zeroVariance_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:06:21.487992+00:00
-- url     : https://prove2.me/theorems/0123ad46-c6db-46ee-8e25-0758ba803d6e
-- title:
--   Characterization of zero relative variance
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   The equality $V=0$ holds if and only if $\rho$ and $\sigma$ commute and admit a common complete orthonormal eigenbasis with eigenvalues $\lambda_x,\mu_x$ and a constant $k>0$ satisfying
--
--   $$\lambda_x\ne0\ \Longrightarrow\ \lambda_x=k\mu_x,\qquad \log k=D.$$
--
--   The two conditions are joint conditions; commutation alone does not imply zero variance. The ratio condition is only on the support of $\rho$, and permits mass of $\sigma$ outside that support.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 17, Section 5: zero relative variance

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

/-- Zero-variance characterization, source PDF p. 17, §5.
The two printed conditions are a conjunction: commutation AND a constant positive
likelihood ratio on supp(rho). A common eigenbasis is exhibited; sigma may have mass
outside supp(rho). Zero ambient eigenvalues are allowed by the p. 5 support compression. -/
theorem zeroVariance_characterization [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma) :
    relativeVarianceNats rho sigma = 0 ↔
      rho * sigma = sigma * rho ∧
      ∃ r : SpectralDecomposition rho, ∃ s : SpectralDecomposition sigma,
        r.basis = s.basis ∧ ∃ k : ℝ, 0 < k ∧
          (∀ x, r.values x ≠ 0 → r.values x = k * s.values x) ∧
          Real.log k = relativeEntropyNats rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
