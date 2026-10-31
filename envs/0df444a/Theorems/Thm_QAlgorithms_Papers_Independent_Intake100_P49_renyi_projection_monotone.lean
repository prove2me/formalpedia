-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_projection_monotone
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_projection_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:38:31.215898+00:00
-- url     : https://prove2.me/theorems/c274dc83-ce85-416d-86b8-113025b44905
-- title:
--   Compression comparison and projection monotonicity
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Assume $\max\{\alpha-1,\alpha/2\}\le z\le\alpha$. For an admissible contraction $K\in\mathcal B(\mathcal H)$ and an orthogonal projection $P$ with $\operatorname{supp}|K|\le P$, $$Q_{\alpha,z}(K\rho K^*\Vert K\sigma K^*)\le Q_{\alpha,z}(P\rho P\Vert P\sigma P).$$ Moreover the latter quantity is increasing in $P$ on the admissible projection domain. This compares arbitrary contractions with their containing subspaces.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 17, Corollary III.34

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

/-- Corollary III.34, PDF p.17, (III.52)--(III.53). L P=L is exactly
support(|L|)<=P for orthogonal P; no zero-exponent CFC is used. -/
theorem renyi_projection_monotone [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (alpha z : ℝ) (ha : 1 < alpha) (hz : 0 < z)
    (hlower : max (alpha - 1) (alpha / 2) ≤ z) (hupper : z ≤ alpha) :
    (∀ L P : H →L[ℂ] H, NonzeroCompressionPair rho sigma L → ‖L‖ ≤ 1 → OrthogonalProjectionOperator P →
      L.comp P = L →
      alphaZQ b alpha z (operatorCompression L rho) (operatorCompression L sigma) ≤
        alphaZQ b alpha z (operatorCompression P rho) (operatorCompression P sigma)) ∧
    (∀ P Q : H →L[ℂ] H, OrthogonalProjectionOperator P → OrthogonalProjectionOperator Q →
      NonzeroCompressionPair rho sigma P → NonzeroCompressionPair rho sigma Q → IsPositive (Q - P) →
      alphaZQ b alpha z (operatorCompression P rho) (operatorCompression P sigma) ≤
        alphaZQ b alpha z (operatorCompression Q rho) (operatorCompression Q sigma)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
