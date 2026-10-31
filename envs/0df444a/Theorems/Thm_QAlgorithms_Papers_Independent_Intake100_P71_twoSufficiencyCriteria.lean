-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_twoSufficiencyCriteria
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.twoSufficiencyCriteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:43:10.949829+00:00
-- url     : https://prove2.me/theorems/979aea67-105f-4c48-a9c4-f58647ea53b1
-- title:
--   Three equivalent criteria for 2-sufficiency
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   A test is any effect $0\le M\le I$, representing rejection of $\rho_0$. Its errors are $\alpha(M)=\operatorname{Tr}(\rho_0M)$ and $\beta(M)=\operatorname{Tr}(\rho_1(I-M))$, with Bayes risk $R_\lambda(M)=\lambda\alpha(M)+(1-\lambda)\beta(M)$ for $0<\lambda<1$. The algebra is 2-sufficient when every test and every such prior admit an effect in $A$ with no greater risk. It is sufficient when one completely positive trace-preserving map $A\to B(H)$ recovers both $\rho_i$ from $E(\rho_i)$.
--
--   Let $\Pi^A_{e,\lambda}=\inf\{R_\lambda(M):M\in A,\ 0\le M\le I\}$ and let $\Pi_{e,\lambda}$ use all ambient effects. Let $P_{t,0},P_{t,+}$ be the full kernel and strictly positive spectral projections of $\rho_1-t\rho_0$, and let $Q_{t,0},Q_{t,+}$ be those of $E(\rho_1)-tE(\rho_0)$ on the same $H$. The following are equivalent:
--
--   $$
--   \begin{aligned}
--   &A\text{ is 2-sufficient};\\
--   &\Pi^A_{e,\lambda}=\Pi_{e,\lambda}\quad\text{for every }0<\lambda<1;\\
--   &Q_{t,0}=P_{t,0}\ \text{and}\ Q_{t,+}=P_{t,+}\quad\text{for every }t\ge0.
--   \end{aligned}
--   $$
--
--   This characterizes preservation of binary testing risks by both spectral projection families.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 10, Lemma 5: three equivalent testing criteria

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

/-- PDF p.10, Lemma 5: 2-sufficiency, equality of all interior-prior testing
risks, and BOTH full-kernel and strictly-positive projection identities.
Restricted projectors act on the SAME ambient Hilbert space. -/
theorem twoSufficiencyCriteria (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef) :
    (TwoSufficient A rho0 rho1 ↔
      ∀ lam : ℝ, 0 < lam → lam < 1 →
        minimalBayesError A rho0 rho1 lam = minimalBayesError ⊤ rho0 rho1 lam) ∧
    ((∀ lam : ℝ, 0 < lam → lam < 1 →
        minimalBayesError A rho0 rho1 lam = minimalBayesError ⊤ rho0 rho1 lam) ↔
      ∀ t : ℝ, 0 ≤ t →
        kernelTest ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho1) ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho0) t = kernelTest rho1 rho0 t ∧
        positiveTest ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho1) ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho0) t = positiveTest rho1 rho0 t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
