-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_twoSufficiencyIffThresholdTests
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.twoSufficiencyIffThresholdTests
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:41:28.890694+00:00
-- url     : https://prove2.me/theorems/7de9488a-1826-4723-a7e1-45b6d684ab1c
-- title:
--   2-sufficiency is equivalent to an optimal test at each threshold
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   A test is any effect $0\le M\le I$, representing rejection of $\rho_0$. Its errors are $\alpha(M)=\operatorname{Tr}(\rho_0M)$ and $\beta(M)=\operatorname{Tr}(\rho_1(I-M))$, with Bayes risk $R_\lambda(M)=\lambda\alpha(M)+(1-\lambda)\beta(M)$ for $0<\lambda<1$. The algebra is 2-sufficient when every test and every such prior admit an effect in $A$ with no greater risk. It is sufficient when one completely positive trace-preserving map $A\to B(H)$ recovers both $\rho_i$ from $E(\rho_i)$.
--
--   At threshold $t\ge0$, a Neyman--Pearson test is an effect maximizing $\operatorname{Tr}((\rho_1-t\rho_0)M)$ over all effects; this definition includes $t=0$ directly.
--
--   Then
--
--   $$
--   A\text{ is 2-sufficient}\quad\Longleftrightarrow\quad
--   \forall t\ge0,\ \exists M_t\in A:\ M_t\text{ is a Neyman--Pearson effect}.
--   $$
--
--   The witness may depend on the threshold. This makes the testing definition usable without choosing a single kernel convention.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 9, Unnumbered: 2-sufficiency iff one optimal test exists at every threshold

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

/-- PDF p.9: 2-sufficiency iff at EACH nonnegative threshold SOME optimal effect
lies in A. At t=0 the threshold objective is used, not an interior prior. -/
theorem twoSufficiencyIffThresholdTests (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef) :
    TwoSufficient A rho0 rho1 ↔
      ∀ t : ℝ, 0 ≤ t → ∃ M : Mat I, M ∈ A ∧ NeymanPearson rho0 rho1 t M := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
