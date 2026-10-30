-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_lemma3_spectralMoments
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.lemma3_spectralMoments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:01:34.562016+00:00
-- url     : https://prove2.me/theorems/0166a62c-3ef3-4321-93b8-401109c475f1
-- title:
--   Lemma 3: classical spectral mean and variance identities
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   Work on the support of $\sigma$, so its eigenvalues are strictly positive. Choose complete orthonormal eigenbases $\{|a_x\rangle\}_x$ and $\{|b_y\rangle\}_y$ with eigenvalues $\lambda_x\ge0$ and $\mu_y>0$. Let $P(x,y)=\lambda_x|\langle b_y|a_x\rangle|^2$ and $L(x,y)=\log(\lambda_x/\mu_y)$, assigned value zero on zero-probability outcomes with $\lambda_x=0$. Then
--
--   $$D=\mathbb E_P L,\qquad V=\mathbb E_P[(L-\mathbb E_P L)^2].$$
--
--   These identities connect the operator-defined quantities to a finite classical law; no positive-variance assumption is imposed.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 8, Lemma 3, equations (14)–(15)

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

/-- Lemma 3, source PDF pp. 7–8, (14)–(15); appendix pp. 17–18.
The supplied eigenbases reconstruct the two states. Sigma has strictly positive eigenvalues,
as in the source's compressed-space convention. No positive-variance assumption is needed. -/
theorem lemma3_spectralMoments [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma)
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma)
    (hmu : ∀ y, 0 < s.values y) :
    relativeEntropyNats rho sigma = spectralLogMean r s ∧
      relativeVarianceNats rho sigma = spectralVariance r s := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
