-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_belavkinEqualityCriteria
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.belavkinEqualityCriteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:39:48.284478+00:00
-- url     : https://prove2.me/theorems/dcd99a2f-ee9c-4c56-84be-72f401966eb7
-- title:
--   Four criteria for equality of Belavkin--Staszewski monotonicity
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   For faithful positive matrices define $S_{\mathrm{BS}}(\sigma,\rho)=\operatorname{Tr}(\rho f(d_{\rho,\sigma}))$, where $f(x)=x\log x$ and the logarithm is natural. The following four conditions are equivalent:
--
--   $$
--   \begin{aligned}
--   &S_{\mathrm{BS}}(\rho_1,\rho_0)=S_{\mathrm{BS}}(E(\rho_1),E(\rho_0));\\
--   &d_{\rho_0,\rho_1}\in N_{\rho_0};\\
--   &\rho_1\rho_0^{-1}\in A;\\
--   &\rho_1\rho_0^{-1}=E(\rho_1)E(\rho_0)^{-1}.
--   \end{aligned}
--   $$
--
--   This relates equality of the entropy loss to an explicit ordered product condition.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 6, Lemma 2: four criteria for equality of Belavkin–Staszewski monotonicity

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

/-- PDF p.6, Lemma 2: ALL four equivalent criteria. Products remain in their
printed noncommuting order. The erroneous Jensen inequality in the proof is
not a target and is not used as a hypothesis. -/
theorem belavkinEqualityCriteria (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef) :
    (belavkinStaszewski rho1 rho0 =
        belavkinStaszewski ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho1) ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho0) ↔
      derivative rho1 rho0 ∈ (algebraMultiplicativeDomain Set.univ (generalizedExpectation A rho0))) ∧
    (derivative rho1 rho0 ∈ (algebraMultiplicativeDomain Set.univ (generalizedExpectation A rho0)) ↔ rho1 * rho0⁻¹ ∈ A) ∧
    (rho1 * rho0⁻¹ ∈ A ↔
      rho1 * rho0⁻¹ = (traceConditionalExpectation Set.univ (A : Set (Mat I))) rho1 * ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho0)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
