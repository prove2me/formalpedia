-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_sufficiencyPreservesTests
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.sufficiencyPreservesTests
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:36:50.357342+00:00
-- url     : https://prove2.me/theorems/4b4a62f4-44d9-4da6-9b36-5681043fbae4
-- title:
--   Sufficiency preserves optimal effects and implies 2-sufficiency
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   A test is any effect $0\le M\le I$, representing rejection of $\rho_0$. Its errors are $\alpha(M)=\operatorname{Tr}(\rho_0M)$ and $\beta(M)=\operatorname{Tr}(\rho_1(I-M))$, with Bayes risk $R_\lambda(M)=\lambda\alpha(M)+(1-\lambda)\beta(M)$ for $0<\lambda<1$. The algebra is 2-sufficient when every test and every such prior admit an effect in $A$ with no greater risk. It is sufficient when one completely positive trace-preserving map $A\to B(H)$ recovers both $\rho_i$ from $E(\rho_i)$.
--
--   At threshold $t\ge0$, a Neyman--Pearson test is an effect maximizing $\operatorname{Tr}((\rho_1-t\rho_0)M)$ over all effects; this definition includes $t=0$ directly. Suppose $A$ is sufficient. Then
--
--   $$
--   E_{\rho_0}=E_{\rho_1},\qquad
--   E_{\rho_0}(M_t)\in A\text{ is Neyman--Pearson whenever }M_t\text{ is Neyman--Pearson},
--   $$
--
--   for every $t\ge0$ and every optimal effect $M_t$. Moreover, $A$ is 2-sufficient.
--
--   This gives the general recovery-to-testing implication while retaining every optimal kernel tie.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 9, Unnumbered: sufficient subalgebras preserve optimal tests and are 2-sufficient

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

/-- PDF p.9 (also p.3): sufficient subalgebras have equal COMPUTED generalized
expectations, preserve every Neyman--Pearson effect under that map, and are
2-sufficient. Equality of the maps is a conclusion, never an assumption. -/
theorem sufficiencyPreservesTests (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef)
    (hs : Sufficient A rho0 rho1) :
    generalizedExpectation A rho0 = generalizedExpectation A rho1 ∧
    (∀ t : ℝ, 0 ≤ t → ∀ M : Mat I, NeymanPearson rho0 rho1 t M →
      generalizedExpectation A rho0 M ∈ A ∧
      NeymanPearson rho0 rho1 t (generalizedExpectation A rho0 M)) ∧
    TwoSufficient A rho0 rho1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
