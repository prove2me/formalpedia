-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_finite_approximation_bounds
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_finite_approximation_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:39:15.634195+00:00
-- url     : https://prove2.me/theorems/12f00b46-8a78-42f0-8dbc-b819b971dd90
-- title:
--   Finite approximation through effects and contractions
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   For $\max\{\alpha-1,\alpha/2\}\le z\le\alpha$, $$Q_{\alpha,z}^{\mathrm{fa}}\le Q_{\alpha,z},\qquad Q_{\alpha,z}^{\mathrm{fa}}=\sup_T Q_{\alpha,z}(T\rho T\Vert T\sigma T)=\sup_K Q_{\alpha,z}(K\rho K^*\Vert K\sigma K^*).$$ Here $T$ ranges over finite-rank effects, $K$ over finite-rank contractions on $\mathcal H$, and both compressed outputs must be nonzero in each domain. These representations identify the same finite approximation. Here $Q^{\mathrm{fa}}$ is the supremum over finite-rank orthogonal projections $P$ such that $P\rho P$ and $P\sigma P$ are both nonzero; $D^{\mathrm{fa}}=(\alpha-1)^{-1}\log Q^{\mathrm{fa}}$.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 18, Lemma III.36

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

/-- Lemma III.36, PDF p.18, (III.54): finite-rank effects and contractions give
the same finite approximation, with nonzero compressed outputs in every domain. -/
theorem renyi_finite_approximation_bounds [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (alpha z : ℝ) (ha : 1 < alpha) (hz : 0 < z)
    (hlower : max (alpha - 1) (alpha / 2) ≤ z) (hupper : z ≤ alpha) :
    renyiQFa b alpha z rho sigma ≤ alphaZQ b alpha z rho sigma ∧
    renyiQFa b alpha z rho sigma =
      sSup {v | ∃ T : H →L[ℂ] H, OperatorEffect T ∧ HasFiniteOperatorRange T ∧ NonzeroCompressionPair rho sigma T ∧
        v = alphaZQ b alpha z (operatorCompression T rho) (operatorCompression T sigma)} ∧
    renyiQFa b alpha z rho sigma =
      sSup {v | ∃ L : H →L[ℂ] H, HasFiniteOperatorRange L ∧ NonzeroCompressionPair rho sigma L ∧ ‖L‖ ≤ 1 ∧
        v = alphaZQ b alpha z (operatorCompression L rho) (operatorCompression L sigma)} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
