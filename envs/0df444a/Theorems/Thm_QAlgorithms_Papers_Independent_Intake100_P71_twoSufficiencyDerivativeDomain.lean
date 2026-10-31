-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_twoSufficiencyDerivativeDomain
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.twoSufficiencyDerivativeDomain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:44:41.203876+00:00
-- url     : https://prove2.me/theorems/ed7e1b28-3603-49a7-9abc-1fa524ded479
-- title:
--   Necessary multiplicative-domain condition, with corrected derivative order
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   A test is any effect $0\le M\le I$, representing rejection of $\rho_0$. Its errors are $\alpha(M)=\operatorname{Tr}(\rho_0M)$ and $\beta(M)=\operatorname{Tr}(\rho_1(I-M))$, with Bayes risk $R_\lambda(M)=\lambda\alpha(M)+(1-\lambda)\beta(M)$ for $0<\lambda<1$. The algebra is 2-sufficient when every test and every such prior admit an effect in $A$ with no greater risk. It is sufficient when one completely positive trace-preserving map $A\to B(H)$ recovers both $\rho_i$ from $E(\rho_i)$.
--
--   If $A$ is 2-sufficient, then
--
--   $$
--   d_{\rho_0,\rho_1}\in N_{\rho_0}.
--   $$
--
--   This is the necessary condition used in the paper's one-copy sufficiency results.
--
--   **Source correction.** The printed theorem has $d_{\rho_1,\rho_0}$; the conclusion above uses $d_{\rho_0,\rho_1}$, the derivative fixed in Lemma 4 and used throughout its proof. The $\rho_0$ similarity calculation and Theorem 5 require this order. Independent moderation of the correction is pending.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 11, Theorem 4: necessary multiplicative-domain condition (corrected derivative order)

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

/-- PDF p.11, Theorem 4, SOURCE CORRECTION: printed d_(rho1,rho0) is changed to
 d_(rho0,rho1), i.e. derivative rho1 rho0 in the accepted interface. The proof
uses the derivative fixed in Lemma 4, and its rho0 similarities require this
order. Independent moderation of this correction remains required. -/
theorem twoSufficiencyDerivativeDomain (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef)
    (htwo : TwoSufficient A rho0 rho1) :
    derivative rho1 rho0 ∈ (algebraMultiplicativeDomain Set.univ (generalizedExpectation A rho0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
