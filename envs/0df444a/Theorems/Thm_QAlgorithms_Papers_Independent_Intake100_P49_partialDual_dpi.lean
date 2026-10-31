-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_partialDual_dpi
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.partialDual_dpi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:46:25.417016+00:00
-- url     : https://prove2.me/theorems/dd520164-5ae7-47ad-9eed-52c9457c7ba6
-- title:
--   Data processing under trace-class or compact domination assumptions
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Let $\Phi:\mathcal B(\mathcal K)\to\mathcal B(\mathcal H)$ be normal, unital and completely positive. Its countable Kraus representation is $\Phi(A)=\sum_i V_i^* A V_i$, in the strong operator topology. The partial dual $\Phi^*(B)=\sum_i V_i B V_i^*$ is defined on a positive bounded $B$ precisely when this strong sum is bounded. Assume either (a) both inputs are trace class, or (b) the partial dual is defined on both, $\sigma$ and $\Phi^*(\sigma)$ are compact, and $\rho\le c\sigma$ for some $c\ge0$. Then $$D^*_{\alpha}(\Phi^*(\rho)\Vert\Phi^*(\sigma))\le D^*_{\alpha}(\rho\Vert\sigma),\qquad\alpha>1.$$ Trace masses are arbitrary. The compact domination alternative need not be trace class.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 35, Corollary IV.14

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

/-- Corollary IV.14, PDF p.35, (IV.123): both alternatives, arbitrary trace
masses, and compactness of both sigma and its dual image in alternative b. -/
theorem partialDual_dpi [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
    {I J : Type*} (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (Phi : HeisenbergOperation H K)
    (hcases : (IsTraceClass rho ∧ IsTraceClass sigma) ∨
      (DualDefined Phi rho ∧ DualDefined Phi sigma ∧ IsCompactOperator sigma ∧
        IsCompactOperator (partialDual Phi sigma) ∧
        ∃ c : ℝ, 0 ≤ c ∧ IsPositive ((c : ℂ) • sigma - rho))) :
    ∀ alpha : ℝ, 1 < alpha →
      alphaZD d alpha alpha (partialDual Phi rho) (partialDual Phi sigma) ≤
        alphaZD b alpha alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
