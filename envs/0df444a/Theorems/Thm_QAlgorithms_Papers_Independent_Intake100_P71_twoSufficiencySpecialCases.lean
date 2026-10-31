-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_twoSufficiencySpecialCases
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.twoSufficiencySpecialCases
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:45:45.320282+00:00
-- url     : https://prove2.me/theorems/b350e5a3-a881-49c6-b245-4d17fd35ebab
-- title:
--   Three separate one-copy regimes imply sufficiency
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   A test is any effect $0\le M\le I$, representing rejection of $\rho_0$. Its errors are $\alpha(M)=\operatorname{Tr}(\rho_0M)$ and $\beta(M)=\operatorname{Tr}(\rho_1(I-M))$, with Bayes risk $R_\lambda(M)=\lambda\alpha(M)+(1-\lambda)\beta(M)$ for $0<\lambda<1$. The algebra is 2-sufficient when every test and every such prior admit an effect in $A$ with no greater risk. It is sufficient when one completely positive trace-preserving map $A\to B(H)$ recovers both $\rho_i$ from $E(\rho_i)$.
--
--   Suppose $A$ is 2-sufficient. If at least one of the following holds: $\rho_0^{it}A\rho_0^{-it}\subseteq A$ for every $t\in\mathbb R$; all pairs of elements of $A$ commute; or $\rho_0\rho_1=\rho_1\rho_0$, then
--
--   $$
--   A\text{ is sufficient for }\{\rho_0,\rho_1\}.
--   $$
--
--   Each of the three conditions separately upgrades testing sufficiency to common completely positive recovery.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 11, Theorem 5: three one-copy regimes where 2-sufficiency implies sufficiency

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

/-- PDF pp.11--12, Theorem 5: each of the three regimes SEPARATELY suffices.
The printed rho0 modular condition, algebra commutativity, and pair commutativity
are alternatives, not simultaneous hypotheses. -/
theorem twoSufficiencySpecialCases (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef)
    (htwo : TwoSufficient A rho0 rho1)
    (hcase : ModularInvariant A rho0 ∨ CommutativeAlgebra A ∨ rho0 * rho1 = rho1 * rho0) :
    Sufficient A rho0 rho1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
