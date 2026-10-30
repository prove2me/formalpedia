-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_supportFailure_arbitraryRates
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.supportFailure_arbitraryRates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:08:57.643431+00:00
-- url     : https://prove2.me/theorems/a078d0f8-618a-478c-bb45-7ce09ccba989
-- title:
--   Non-nested supports allow arbitrarily large finite exponents
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on the same nonzero finite-dimensional Hilbert space, and suppose $\operatorname{supp}\rho\not\subseteq\operatorname{supp}\sigma$. Optimize over all binary POVMs on the tensor powers, with conditional errors $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Then
--
--   $$D(\rho\Vert\sigma)=+\infty,\qquad\forall R\in\mathbb R,\quad\lim_{n\to\infty}\min_{A:\,\beta_n(A)\le e^{-nR}}\alpha_n(A)=0.$$
--
--   Every finite rate is allowed. This explains the support restriction for finite relative-entropy second-order formulas; no product with an infinite rate is formed.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 5, Section 2: support-domain exclusion

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

/-- Non-nested supports, source PDF p. 5 (and relative-entropy definition p. 3).
The relative entropy is infinite; for every fixed finite first-order rate R the
optimal type-I error tends to zero under beta<=exp(-nR). This asserts a limit,
not an identically zero finite-sample error, and never forms n times infinity. -/
theorem supportFailure_arbitraryRates [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : ¬ SupportIncluded rho sigma) :
    QuantumLoss.umegakiEntropy rho sigma hrho hsigma = ⊤ ∧
      ∀ R : ℝ, Tendsto (constrainedTypeI rho sigma R 0 (fun _ => 0)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
