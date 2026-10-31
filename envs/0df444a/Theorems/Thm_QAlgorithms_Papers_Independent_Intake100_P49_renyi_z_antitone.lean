-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_z_antitone
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_z_antitone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:31:46.561992+00:00
-- url     : https://prove2.me/theorems/d8506281-f543-43c2-9550-24640e27cb18
-- title:
--   Renyi quantities decrease with z
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   For fixed $\alpha>1$ and $0<z\le z^{\prime}$, $$Q_{\alpha,z^{\prime}}\le Q_{\alpha,z},\qquad D_{\alpha,z^{\prime}}\le D_{\alpha,z}.$$ The same inequality holds for $\widetilde D$ when both inputs are trace class. If $\mathcal L^{\alpha,z}$ denotes the relative bounded class with finite $z$-power trace, then $\mathcal L^{\alpha,z}(\mathcal H,\sigma)\subseteq\mathcal L^{\alpha,z^{\prime}}(\mathcal H,\sigma)$. These comparisons preserve infinite values.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 9, Proposition III.16

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

/-- Proposition III.16, PDF p.9: Q,D,Dtilde decrease in z; relative Schatten
classes increase. Only the Dtilde clause needs both inputs trace-class. -/
theorem renyi_z_antitone [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (alpha : ℝ) (ha : 1 < alpha) :
    AntitoneOn (fun z => alphaZQ b alpha z rho sigma) (Set.Ioi 0) ∧
    AntitoneOn (fun z => alphaZD b alpha z rho sigma) (Set.Ioi 0) ∧
    (IsTraceClass rho → IsTraceClass sigma →
      AntitoneOn (fun z => renyiDTilde b alpha z rho sigma) (Set.Ioi 0)) ∧
    (∀ z zprime : ℝ, 0 < z → z ≤ zprime → relativeSchatten b alpha z rho sigma →
      relativeSchatten b alpha zprime rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
