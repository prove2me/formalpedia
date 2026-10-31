-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_support_failure
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_support_failure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:40:43.241292+00:00
-- url     : https://prove2.me/theorems/a7d398be-4319-4df2-b650-b40a1f9e96aa
-- title:
--   Support failure gives infinite Q and finite approximation
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   If the closed support of $\rho$ is not contained in that of $\sigma$, then for every $\alpha>1,z>0$, $$Q_{\alpha,z}^{\mathrm{fa}}(\rho\Vert\sigma)=Q_{\alpha,z}(\rho\Vert\sigma)=+\infty.$$ No trace-class assumption or invertibility is required. This describes the support obstruction. Here $Q^{\mathrm{fa}}$ is the supremum over finite-rank orthogonal projections $P$ such that $P\rho P$ and $P\sigma P$ are both nonzero; $D^{\mathrm{fa}}=(\alpha-1)^{-1}\log Q^{\mathrm{fa}}$.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 19, Lemma III.41

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

/-- Lemma III.41, PDF p.19, (III.61): closed-support failure makes Q and its
finite approximation infinite. Kernel inclusion is the exact dual condition. -/
theorem renyi_support_failure [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (hsupport : ¬ (LinearMap.ker sigma.toLinearMap ≤ LinearMap.ker rho.toLinearMap))
    (alpha z : ℝ) (ha : 1 < alpha) (hz : 0 < z) :
    renyiQFa b alpha z rho sigma = ⊤ ∧ alphaZQ b alpha z rho sigma = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
