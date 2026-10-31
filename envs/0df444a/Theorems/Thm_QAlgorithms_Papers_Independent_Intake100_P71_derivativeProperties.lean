-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_derivativeProperties
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.derivativeProperties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:38:32.497549+00:00
-- url     : https://prove2.me/theorems/c3e9466e-3a60-46e8-9936-c80ba2787137
-- title:
--   Derivative characterization, positivity, norm domination and restriction
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Let $A\subseteq B(H)$ be a concrete unital star subalgebra with the same identity, and let $E:B(H)\to A$ be its unique ordinary-trace-preserving conditional expectation. Write $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$, $F_\rho=\{X:E_\rho(X)=X\}$ and $N_\rho=\{X:E_\rho(X^*X)=E_\rho(X)^*E_\rho(X),\ E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*\}$. Write $d_{\rho_0,\rho_1}=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$.
--
--   Define the weighted form $\langle X,Y\rangle_{\rho_0}=\operatorname{Tr}(X^*\rho_0^{1/2}Y\rho_0^{1/2})$, conjugate-linear in its first argument. The derivative is characterized uniquely by
--
--   $$
--   \bigl[\forall X\in B(H),\ \operatorname{Tr}(\rho_1X)=\langle X^*,D\rangle_{\rho_0}\bigr]
--   \quad\Longleftrightarrow\quad D=d_{\rho_0,\rho_1}.
--   $$
--
--   It is positive, and for every real $c>0$ with $\rho_1\le c\rho_0$ it satisfies $\|d_{\rho_0,\rho_1}\|_{\mathrm{op}}\le c$. Furthermore,
--
--   $$
--   E_{\rho_0}(d_{\rho_0,\rho_1})=d_{E(\rho_0),E(\rho_1)}.
--   $$
--
--   These facts pin the derivative's order, normalization and behavior under restriction.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 5, Unnumbered: derivative characterization, positivity, norm bound and restriction identity

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

/-- PDF p.5, section 2.2: unique weighted-pairing characterization, positivity,
operator norm domination and restriction identity for the computed derivative.
The input of weightedPair is X*, as printed; its first argument is conjugated. -/
theorem derivativeProperties (A : Alg I) (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef) :
    (∀ D : Mat I, (∀ X : Mat I, (rho1 * X).trace = weightedPair rho0 Xᴴ D) ↔
      D = derivative rho1 rho0) ∧
    (derivative rho1 rho0).PosSemidef ∧
    (∀ lam : ℝ, 0 < lam → LE rho1 ((lam : ℂ) • rho0) →
      specNorm (derivative rho1 rho0) ≤ lam) ∧
    generalizedExpectation A rho0 (derivative rho1 rho0) =
      derivative ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho1) ((traceConditionalExpectation Set.univ (A : Set (Mat I))) rho0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
