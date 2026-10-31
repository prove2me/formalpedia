-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_commutativeDomains
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.commutativeDomains
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:46:43.453596+00:00
-- url     : https://prove2.me/theorems/47980ea7-de58-4192-b387-f5b0b8ebb0a6
-- title:
--   A commutative algebra has equal fixed and multiplicative domains
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty. Let $\rho$ be a positive definite positive density matrix with ordinary trace one, and let $A\subseteq B(H)$ be a concrete unital star subalgebra sharing its identity. Let $E$ be the ordinary-trace-preserving conditional expectation onto $A$, and define $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$. Its fixed points form $F_\rho$, and its multiplicative domain $N_\rho$ consists of all ambient $X$ satisfying both $E_\rho(X^*X)=E_\rho(X)^*E_\rho(X)$ and $E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*$.
--
--   If every pair of elements of $A$ commutes, then
--
--   $$
--   N_\rho=F_\rho.
--   $$
--
--   This is the explicit unnumbered assertion after Theorem 5, without an additional density pair or testing hypothesis.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 12, Unnumbered: a commutative subalgebra has N_rho=F_rho

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

/-- PDF p.12, unnumbered assertion: a commutative subalgebra has equal
multiplicative domain and fixed points for ANY faithful density. No pair
or 2-sufficiency hypothesis is added. -/
theorem commutativeDomains (A : Alg I) (rho : Mat I)
    (h : IsDensityMatrix rho) (hf : rho.PosDef)
    (hcomm : CommutativeAlgebra A) :
    (algebraMultiplicativeDomain Set.univ (generalizedExpectation A rho)) = fixedDomain A rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
