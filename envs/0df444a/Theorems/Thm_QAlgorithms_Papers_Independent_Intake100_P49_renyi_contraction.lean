-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_contraction
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:37:58.574753+00:00
-- url     : https://prove2.me/theorems/d3543616-fd78-4266-b1b8-c29727428f1a
-- title:
--   Alpha-z Q decreases under admissible contractions
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Let $K:\mathcal H\to\mathcal K$ be bounded with $\|K\|\le1$ and with $K\rho K^*$ and $K\sigma K^*$ nonzero. If $\max\{\alpha-1,\alpha/2\}\le z\le\alpha$, then $$Q_{\alpha,z}(K\rho K^*\Vert K\sigma K^*)\le Q_{\alpha,z}(\rho\Vert\sigma).$$ The input need not be trace class and the Hilbert spaces may differ.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 16, Lemma III.32

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

/-- Lemma III.32, PDF p.16, (III.48): contraction H -> K, exact parameter
interval, and nonzero compressed outputs, without a trace-class assumption. -/
theorem renyi_contraction [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
    {I J : Type*} (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (L : H →L[ℂ] K) (hL : NonzeroCompressionPair rho sigma L) (hcontract : ‖L‖ ≤ 1)
    (alpha z : ℝ) (ha : 1 < alpha) (hz : 0 < z)
    (hlower : max (alpha - 1) (alpha / 2) ≤ z) (hupper : z ≤ alpha) :
    alphaZQ d alpha z (operatorCompression L rho) (operatorCompression L sigma) ≤ alphaZQ b alpha z rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
