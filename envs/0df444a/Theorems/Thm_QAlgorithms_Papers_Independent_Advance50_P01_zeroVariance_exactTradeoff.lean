-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_zeroVariance_exactTradeoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.zeroVariance_exactTradeoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:07:45.482983+00:00
-- url     : https://prove2.me/theorems/ec7935a5-fb63-41cb-8d7d-bc75eb708bba
-- title:
--   Exact optimal tradeoff at zero relative variance
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   Assume $V=0$. For every positive integer $n$ and every $0\le\varepsilon\le1$, the optimal type-II error at type-I tolerance $\varepsilon$ is
--
--   $$\beta_n^*(\varepsilon)=(1-\varepsilon)e^{-nD}.$$
--
--   A binary POVM attains this value with type-I error exactly $\varepsilon$. Thus the optimal frontier is $\alpha_n=1-\beta_n e^{nD}$. When $\varepsilon<1$ its finite logarithmic form is
--
--   $$-\log\beta_n^*(\varepsilon)=nD-\log(1-\varepsilon).$$
--
--   Fractional acceptance effects give every tolerance, including both endpoints; the frontier is not an identity for arbitrary tests.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 17, Section 5: exact optimal frontier

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

/-- Exact optimal tradeoff at V=0, source PDF p. 17, §5.
The identity describes the optimal frontier, not every test. Fractional effects give
all epsilon in [0,1]; the logarithmic formula excludes epsilon=1. -/
theorem zeroVariance_exactTradeoff [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma) (hV : relativeVarianceNats rho sigma = 0)
    (n : ℕ) (hn : 1 ≤ n) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon ∧ epsilon ≤ 1) :
    iidOptimalBeta rho sigma n epsilon =
        (1 - epsilon) * Real.exp (-(n * relativeEntropyNats rho sigma)) ∧
    (∃ A : IIDTest I n, iidTypeI rho A = epsilon ∧
      typeII sigma A = iidOptimalBeta rho sigma n epsilon) ∧
    (epsilon < 1 → iidTestingDivergenceNats rho sigma n epsilon =
      ((n * relativeEntropyNats rho sigma - Real.log (1 - epsilon) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
