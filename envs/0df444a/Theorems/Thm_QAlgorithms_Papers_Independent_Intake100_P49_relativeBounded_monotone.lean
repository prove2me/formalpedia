-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_relativeBounded_monotone
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.relativeBounded_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:30:29.475268+00:00
-- url     : https://prove2.me/theorems/c117ef15-7a0f-418c-81f0-dd2d806073f7
-- title:
--   Relative bounded classes increase with z
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Fix $\alpha>1$. Write $\mathcal B^{\alpha,z}(\mathcal H,\sigma)$ for the nonzero PSD operators with the bounded reduced factorization above. Then $$0<z<z^{\prime}\quad\Longrightarrow\quad\mathcal B^{\alpha,z}(\mathcal H,\sigma)\subseteq\mathcal B^{\alpha,z^{\prime}}(\mathcal H,\sigma).$$ This identifies the direction of the relative bounded-class inclusion.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 7, Lemma III.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P49

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass TraceClass traceNormTopology)

open QAlgorithms.Papers.Independent.Bridge50.P48 (hilbertPositiveTrace)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Lemma III.4, PDF p.7: relative bounded classes increase in z. -/
theorem relativeBounded_monotone [TopologicalSpace.SeparableSpace H]
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (alpha z zprime : ℝ) (ha : 1 < alpha) (hz : 0 < z) (hzz : z < zprime) :
    relativeBounded alpha z rho sigma → relativeBounded alpha zprime rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
