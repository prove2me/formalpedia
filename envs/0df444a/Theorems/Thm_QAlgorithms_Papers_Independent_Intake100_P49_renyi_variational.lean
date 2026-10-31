-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_renyi_variational
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.renyi_variational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:33:26.966088+00:00
-- url     : https://prove2.me/theorems/ee0bf3b4-f115-4bfb-bf63-d99da3d2c43b
-- title:
--   Extended alpha-z variational supremum formulas
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Assume either (a) $\rho\notin\mathcal B^{\alpha,z}$, (b) $\rho\in\mathcal B^{\alpha,z}\setminus\mathcal L^{\alpha,z}$ and $\sigma$ is compact, or (c) $\rho\in\mathcal L^{\alpha,z}$. For bounded PSD $A$, define $F(A)=\operatorname{Tr}[(A^{1/2}\rho^{\alpha/z}A^{1/2})^{z/\alpha}]$ and $G(A)=\operatorname{Tr}[(A^{1/2}\sigma^{(\alpha-1)/z}A^{1/2})^{z/(\alpha-1)}]$. Then $$Q_{\alpha,z}=\sup_{A\ge0,\,G(A)<\infty}\{\alpha F(A)+(1-\alpha)G(A)\},\qquad \log Q_{\alpha,z}=\sup_{A\ge0,\,0<G(A)<\infty}\{\alpha\log F(A)+(1-\alpha)\log G(A)\}.$$ The first supremum is unchanged by requiring $G(A)>0$. In cases (a),(b), and also in case (c) when $\sigma$ is compact, each of these domains can additionally be restricted to finite-rank $A$. The first domain includes $A=0$. These are extended variational representations with finite penalty, not an all-operator negative-order formula.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 12, Lemma III.23

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

/-- Lemma III.23, PDF p.12, (III.31)--(III.32): powers inside both traces,
all three domains, and the finite-rank refinements under the source alternatives. -/
theorem renyi_variational [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (alpha z : ℝ) (ha : 1 < alpha) (hz : 0 < z)
    (hcases : VariationalHypothesis b alpha z rho sigma) :
    (alphaZQ b alpha z rho sigma : EReal) =
      sSup {v | ∃ A, FinitePenalty b alpha z sigma A ∧ v = additivePayoff b alpha z rho sigma A} ∧
    ENNReal.log (alphaZQ b alpha z rho sigma) =
      sSup {v | ∃ A, PositiveFinitePenalty b alpha z sigma A ∧
        v = logarithmicPayoff b alpha z rho sigma A} ∧
    (alphaZQ b alpha z rho sigma : EReal) =
      sSup {v | ∃ A, PositiveFinitePenalty b alpha z sigma A ∧
        v = additivePayoff b alpha z rho sigma A} ∧
    ((¬ relativeBounded alpha z rho sigma ∨ IsCompactOperator sigma) →
      (alphaZQ b alpha z rho sigma : EReal) =
        sSup {v | ∃ A, FinitePenalty b alpha z sigma A ∧ HasFiniteOperatorRange A ∧
          v = additivePayoff b alpha z rho sigma A} ∧
      ENNReal.log (alphaZQ b alpha z rho sigma) =
        sSup {v | ∃ A, PositiveFinitePenalty b alpha z sigma A ∧ HasFiniteOperatorRange A ∧
          v = logarithmicPayoff b alpha z rho sigma A} ∧
      (alphaZQ b alpha z rho sigma : EReal) =
        sSup {v | ∃ A, PositiveFinitePenalty b alpha z sigma A ∧ HasFiniteOperatorRange A ∧
          v = additivePayoff b alpha z rho sigma A}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
