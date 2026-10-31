-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_positive
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:32:25.579147+00:00
-- url     : https://prove2.me/theorems/210478cd-9e25-493a-8207-bbe5a4b50454
-- title:
--   Strict positivity of Q and exclusion of minus infinity for D
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   For every $\alpha>1,z>0$, $$Q_{\alpha,z}(\rho\Vert\sigma)>0,\qquad D_{\alpha,z}(\rho\Vert\sigma)>-\infty.$$ Either quantity may equal $+\infty$. These bounds prevent zero-times-infinity and infinity-minus-infinity ambiguities in subsequent identities.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 11, Lemma III.20

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

/-- Lemma III.20, PDF p.11, (III.26): Q>0 and D>-infinity, allowing +infinity. -/
theorem renyi_positive [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (alpha z : ℝ) (ha : 1 < alpha) (hz : 0 < z) :
    0 < alphaZQ b alpha z rho sigma ∧ ⊥ < alphaZD b alpha z rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
