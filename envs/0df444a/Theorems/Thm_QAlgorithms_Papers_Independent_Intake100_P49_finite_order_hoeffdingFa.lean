-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_finite_order_hoeffdingFa
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.finite_order_hoeffdingFa
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:43:47.523964+00:00
-- url     : https://prove2.me/theorems/4838cc43-b6ad-4d75-9a4a-b56c3689ae2a
-- title:
--   Finite Renyi order equates ordinary-fa anti-divergences
-- statement:
--   Let $\mathcal H$ (and, when needed, $\mathcal K$) be complex separable complete Hilbert spaces. Unless density operators are specified, $\rho,\sigma$ are arbitrary nonzero bounded positive semidefinite operators. Positive traces take values in $[0,+\infty]$, all logarithms are natural, and divergences retain both extended endpoints. For $\alpha>1,z>0$, $Q_{\alpha,z}(\rho\Vert\sigma)$ is the trace of the $z$th power of the unique reduced positive bounded solution $R$ to $\rho^{\alpha/z}=\sigma^{(\alpha-1)/(2z)}R\sigma^{(\alpha-1)/(2z)}$, with $\ker\sigma\subseteq\ker R$, and is $+\infty$ if no such solution exists. Write $D_{\alpha,z}=(\alpha-1)^{-1}\log Q_{\alpha,z}$, $\widetilde D_{\alpha,z}=D_{\alpha,z}-(\alpha-1)^{-1}\log\operatorname{Tr}\rho$ when the inputs are trace class, and use a star when $z=\alpha$. Write $\mathcal B^{\alpha,z}$ for the nonzero PSD factorization class and $\mathcal L^{\alpha,z}$ for its subset with finite $Q$.
--
--   Define $\widetilde\psi(u)=(1-u)\log Q^*_{1/(1-u)}$ for $0<u<1$, with endpoint values $\widetilde\psi(0)=\log\operatorname{Tr}\rho$ and $\widetilde\psi(1)=D_{\max}$. Let $\widetilde\psi^{\mathrm{fa}}$ be its finite-projection supremum. If $D^*_{\alpha_0}<+\infty$ for some $\alpha_0>1$, then for every real $r$, $$H_r^{*,\mathrm{fa}}:=\sup_{0<u<1}\{ur-\widetilde\psi^{\mathrm{fa}}(u)\}=\widehat H_r^{*,\mathrm{fa}}:=\max_{0\le u\le1}\{ur-\widetilde\psi^{\mathrm{fa}}(u)\}.$$ The maximum is attained. This statement concerns ordinary finite approximation and does not regularize by tensor powers. Here $Q^{\mathrm{fa}}$ is the supremum over finite-rank orthogonal projections $P$ such that $P\rho P$ and $P\sigma P$ are both nonzero; $D^{\mathrm{fa}}=(\alpha-1)^{-1}\log Q^{\mathrm{fa}}$.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 24, Lemma III.54

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

/-- Lemma III.54, PDF p.24, (III.87): ordinary finite-approximation open and
closed anti-divergences agree under finiteness at some Renyi order above one. -/
theorem finite_order_hoeffdingFa [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : NonzeroPositive rho) (hsigma : NonzeroPositive sigma)
    (hfinite : ∃ alpha0 : ℝ, 1 < alpha0 ∧ alphaZD b alpha0 alpha0 rho sigma < ⊤) :
    ∀ r : ℝ, hoeffdingFa b r rho sigma = hatHoeffdingFa b r rho sigma ∧
      ∃ u : Set.Icc (0 : ℝ) 1,
        ((u.val * r : ℝ) : EReal) - tildePsiFa b u.val rho sigma =
          hatHoeffdingFa b r rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
