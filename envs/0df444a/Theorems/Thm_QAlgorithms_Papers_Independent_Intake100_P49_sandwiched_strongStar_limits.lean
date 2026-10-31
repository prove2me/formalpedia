-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_sandwiched_strongStar_limits
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.sandwiched_strongStar_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:39:57.58851+00:00
-- url     : https://prove2.me/theorems/1a6be8c8-51f6-482f-950e-1bf165951cfe
-- title:
--   Strong-star compression limits
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Assume both inputs trace class and fix $\alpha>1$. If admissible contractions $K_n:\mathcal H\to\mathcal K$ converge strongly to admissible $K_\infty$ and their adjoints converge strongly, let $q_n=Q^*_\alpha(K_n\rho K_n^*\Vert K_n\sigma K_n^*)$. Then $$Q^*_\alpha(K_\infty\rho K_\infty^*\Vert K_\infty\sigma K_\infty^*)\le\liminf_n q_n\le\limsup_n q_n\le Q^*_\alpha(\rho\Vert\sigma).$$ Independently, if admissible orthogonal projections $P_n$ converge strongly to $P_\infty$ with $P_\infty\rho P_\infty=\rho$ and $P_\infty\sigma P_\infty=\sigma$, then $Q^*_\alpha(P_n\rho P_n\Vert P_n\sigma P_n)\to Q^*_\alpha(\rho\Vert\sigma)$. These are extended convergence statements.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 18, Lemma III.38

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

/-- Lemma III.38, PDF p.18, (III.57)--(III.58): strong-star contractions and
the full projection-sequence consequence; alpha>1 is fixed by the preceding paragraph. -/
theorem sandwiched_strongStar_limits [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace.SeparableSpace K] {I J : Type*}
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (htrho : IsTraceClass rho) (htsigma : IsTraceClass sigma)
    (alpha : ℝ) (ha : 1 < alpha) :
    (∀ (L : ℕ → H →L[ℂ] K) (M : H →L[ℂ] K),
      (∀ n, NonzeroCompressionPair rho sigma (L n)) → (∀ n, ‖L n‖ ≤ 1) →
      NonzeroCompressionPair rho sigma M → OperatorStrongLimit L M →
      OperatorStrongLimit (fun n => (L n).adjoint) M.adjoint →
      let q := fun n => alphaZQ d alpha alpha (operatorCompression (L n) rho) (operatorCompression (L n) sigma)
      alphaZQ d alpha alpha (operatorCompression M rho) (operatorCompression M sigma) ≤ liminf q atTop ∧
      liminf q atTop ≤ limsup q atTop ∧ limsup q atTop ≤ alphaZQ b alpha alpha rho sigma) ∧
    (∀ (P : ℕ → H →L[ℂ] H) (Pinf : H →L[ℂ] H),
      (∀ n, OrthogonalProjectionOperator (P n) ∧ NonzeroCompressionPair rho sigma (P n)) →
      OperatorStrongLimit P Pinf → Pinf * rho * Pinf = rho → Pinf * sigma * Pinf = sigma →
      Tendsto (fun n => alphaZQ b alpha alpha (operatorCompression (P n) rho) (operatorCompression (P n) sigma))
        atTop (nhds (alphaZQ b alpha alpha rho sigma))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
