-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_sandwiched_order_limit
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.sandwiched_order_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:41:55.682885+00:00
-- url     : https://prove2.me/theorems/1a08c77c-8a8c-412b-8ae9-78899888eacc
-- title:
--   Sandwiched order monotonicity and infinite-order limits
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   For nonzero positive trace-class inputs, $\alpha\mapsto\widetilde D^*_\alpha$ is increasing on $(1,\infty)$ and $$\lim_{\alpha\to\infty}\widetilde D^*_\alpha(\rho\Vert\sigma)=\lim_{\alpha\to\infty}D^*_\alpha(\rho\Vert\sigma)=D_{\max}(\rho\Vert\sigma).$$ Here $D_{\max}=\log\inf\{c>0:\rho\le c\sigma\}$, with an empty infimum equal to $+\infty$. No trace-one or support hypothesis is imposed.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 19, Corollary III.42

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

/-- Corollary III.42, PDF p.19, (III.62)--(III.63): trace-normalized monotonicity
and both order limits, with arbitrary positive finite trace masses. -/
theorem sandwiched_order_limit [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (htrho : IsTraceClass rho) (htsigma : IsTraceClass sigma) :
    MonotoneOn (fun alpha => renyiDTilde b alpha alpha rho sigma) (Set.Ioi 1) ∧
    Tendsto (fun alpha => renyiDTilde b alpha alpha rho sigma) atTop (nhds (maxD rho sigma)) ∧
    Tendsto (fun alpha => alphaZD b alpha alpha rho sigma) atTop (nhds (maxD rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
