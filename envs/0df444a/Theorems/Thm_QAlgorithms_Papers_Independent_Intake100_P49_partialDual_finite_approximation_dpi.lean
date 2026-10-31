-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_partialDual_finite_approximation_dpi
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.partialDual_finite_approximation_dpi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:45:43.162378+00:00
-- url     : https://prove2.me/theorems/0aaa7b42-d555-49ef-8a48-7264e930bf98
-- title:
--   Partial-dual data processing with output finite approximation
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Let $\Phi:\mathcal B(\mathcal K)\to\mathcal B(\mathcal H)$ be normal, unital and completely positive. Its countable Kraus representation is $\Phi(A)=\sum_i V_i^* A V_i$, in the strong operator topology. The partial dual $\Phi^*(B)=\sum_i V_i B V_i^*$ is defined on a positive bounded $B$ precisely when this strong sum is bounded. Assume $\Phi^*$ is defined on $\rho,\sigma$ and $D_{\alpha}^{*,\mathrm{fa}}(\rho\Vert\sigma)=D^*_{\alpha}(\rho\Vert\sigma)$ for every $\alpha>1$. Then $$D_{\alpha}^{*,\mathrm{fa}}(\Phi^*(\rho)\Vert\Phi^*(\sigma))\le D^*_{\alpha}(\rho\Vert\sigma),\qquad\alpha>1.$$ No output approximability or finite-Renyi-order premise is imposed. This preserves finite approximation on the output. Here $Q^{\mathrm{fa}}$ is the supremum over finite-rank orthogonal projections $P$ such that $P\rho P$ and $P\sigma P$ are both nonzero; $D^{\mathrm{fa}}=(\alpha-1)^{-1}\log Q^{\mathrm{fa}}$.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 35, Theorem IV.13

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

/-- Theorem IV.13, PDF p.35, (IV.121)--(IV.122): output retains fa. Definedness
refers to Phi*, resolving the printed missing noun/domain mismatch via p.34. -/
theorem partialDual_finite_approximation_dpi [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace.SeparableSpace K] {I J : Type*}
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (happrox : ∀ alpha : ℝ, 1 < alpha →
      renyiDFa b alpha alpha rho sigma = alphaZD b alpha alpha rho sigma)
    (Phi : HeisenbergOperation H K) (hDrho : DualDefined Phi rho) (hDsigma : DualDefined Phi sigma) :
    ∀ alpha : ℝ, 1 < alpha →
      renyiDFa d alpha alpha (partialDual Phi rho) (partialDual Phi sigma) ≤
        alphaZD b alpha alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
