-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_testingRiskTraceNormCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.testingRiskTraceNormCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:43:53.243912+00:00
-- url     : https://prove2.me/theorems/bace2609-b01b-4141-87b2-3087774bfb15
-- title:
--   Trace-norm criterion for equality of testing risks
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   A test is any effect $0\le M\le I$, representing rejection of $\rho_0$. Its errors are $\alpha(M)=\operatorname{Tr}(\rho_0M)$ and $\beta(M)=\operatorname{Tr}(\rho_1(I-M))$, with Bayes risk $R_\lambda(M)=\lambda\alpha(M)+(1-\lambda)\beta(M)$ for $0<\lambda<1$. The algebra is 2-sufficient when every test and every such prior admit an effect in $A$ with no greater risk. It is sufficient when one completely positive trace-preserving map $A\to B(H)$ recovers both $\rho_i$ from $E(\rho_i)$.
--
--   Let $\Pi^A_{e,\lambda}$ and $\Pi_{e,\lambda}$ denote infima of $R_\lambda$ over effects in $A$ and over all ambient effects, respectively. Write $\|X\|_1=\operatorname{Tr}\sqrt{X^*X}$. Then
--
--   $$
--   \bigl[\forall\lambda\in(0,1),\ \Pi^A_{e,\lambda}=\Pi_{e,\lambda}\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\forall t\ge0,\ \|E(\rho_1)-tE(\rho_0)\|_1\ge\|\rho_1-t\rho_0\|_1\bigr].
--   $$
--
--   This translates lossless testing to the trace-norm comparison printed in the source.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 10, Unnumbered: trace-norm criterion for equality of testing risks

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P71

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P71

open scoped Matrix ComplexOrder ComplexConjugate BigOperators

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Support50.P12 (Alg)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

open QAlgorithms.Papers.Independent.Bridge50.P31
  (traceConditionalExpectation stateDual algebraMultiplicativeDomain fixedPoints
   AlgebraChannel derivative weightedPair positiveTest kernelTest)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I] [nonemptyI : Nonempty I]

include nonemptyI

/-- PDF p.10: equality of all restricted and unrestricted minimum Bayes errors
iff the PRINTED greater-than-or-equal trace-norm comparison holds at all t>=0. -/
theorem testingRiskTraceNormCriterion (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef) :
    (∀ lam : ℝ, 0 < lam → lam < 1 →
      minimalBayesError A rho0 rho1 lam = minimalBayesError ⊤ rho0 rho1 lam) ↔
    (∀ t : ℝ, 0 ≤ t →
      traceNorm (rho1 - (t : ℂ) • rho0) ≤
        traceNorm ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho1 - (t : ℂ) • (traceConditionalExpectation Set.univ (A : Set (Mat I))) rho0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
