-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_sandwiched_max_characterizations
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.sandwiched_max_characterizations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:42:40.488411+00:00
-- url     : https://prove2.me/theorems/14d9552e-ee81-4e9d-9767-c4eeb6d31d28
-- title:
--   Max-relative entropy from orders, domination and tests
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   For nonzero positive trace-class inputs, $\widetilde D^*_\alpha$ increases in $\alpha>1$ and $$\sup_{\alpha>1}\widetilde D^*_\alpha=\lim_{\alpha\to\infty}\widetilde D^*_\alpha=\lim_{\alpha\to\infty}D^*_\alpha=D_{\max}=\log\inf\{c>0:\rho\le c\sigma\}=\log\sup_{0\le T\le I,\,\operatorname{Tr}\sigma T>0}\frac{\operatorname{Tr}\rho T}{\operatorname{Tr}\sigma T}.$$ All optimizations retain infinite values. The ratio formula uses every quantum effect with strictly positive denominator, and characterizes the same domination gauge.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 21, Corollary III.45

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

/-- Corollary III.45, PDF p.21, (III.65)--(III.69): complete supremum, limit,
order-gauge and test-ratio characterizations, including positive test denominator. -/
theorem sandwiched_max_characterizations [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (htrho : IsTraceClass rho) (htsigma : IsTraceClass sigma) :
    MonotoneOn (fun alpha => renyiDTilde b alpha alpha rho sigma) (Set.Ioi 1) ∧
    (⨆ alpha : Set.Ioi (1 : ℝ), renyiDTilde b alpha.val alpha.val rho sigma) = maxD rho sigma ∧
    Tendsto (fun alpha => renyiDTilde b alpha alpha rho sigma) atTop (nhds (maxD rho sigma)) ∧
    Tendsto (fun alpha => alphaZD b alpha alpha rho sigma) atTop (nhds (maxD rho sigma)) ∧
    maxD rho sigma = ENNReal.log
      (sInf {v : ℝ≥0∞ | ∃ c : ℝ, 0 < c ∧ IsPositive ((c : ℂ) • sigma - rho) ∧
        v = ENNReal.ofReal c}) ∧
    maxD rho sigma = ENNReal.log
      (sSup {v : ℝ≥0∞ | ∃ T : H →L[ℂ] H, OperatorEffect T ∧
        0 < hilbertPositiveTrace b (positiveSpectralPower T (1 / 2) * sigma * positiveSpectralPower T (1 / 2)) ∧
        v = hilbertPositiveTrace b (positiveSpectralPower T (1 / 2) * rho * positiveSpectralPower T (1 / 2)) /
          hilbertPositiveTrace b (positiveSpectralPower T (1 / 2) * sigma * positiveSpectralPower T (1 / 2))}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
