-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_lowerSemicontinuous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:36:49.769954+00:00
-- url     : https://prove2.me/theorems/e2420790-17cf-4a1b-8a0d-5624d57187fb
-- title:
--   Trace-norm lower semicontinuity
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   For every $\alpha>1$ and $z\ge\alpha$, $$ (\rho,\sigma)\longmapsto Q_{\alpha,z}(\rho\Vert\sigma),\qquad (\rho,\sigma)\longmapsto D_{\alpha,z}(\rho\Vert\sigma) $$ are lower semicontinuous on their positive nonzero trace-class domain with the product trace-norm topology. This is a trace-norm assertion even on infinite-dimensional spaces.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 16, Corollary III.30

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

/-- Corollary III.30, PDF p.16: lower semicontinuity in trace-norm topology,
on the positive nonzero trace-class domain where the source defines Q,D. -/
theorem renyi_lowerSemicontinuous [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ) (ha : 1 < alpha) (hz : alpha ≤ z) :
    letI : TopologicalSpace (TraceClass H) := traceNormTopology
    let domain := {A : TraceClass H // NonzeroPositive A.val}
    LowerSemicontinuous (fun pair : domain × domain =>
      alphaZQ b alpha z pair.1.val.val pair.2.val.val) ∧
    LowerSemicontinuous (fun pair : domain × domain =>
      alphaZD b alpha z pair.1.val.val pair.2.val.val) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
