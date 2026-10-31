-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_multiplicativeDomainSimilarities
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.multiplicativeDomainSimilarities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:37:38.886324+00:00
-- url     : https://prove2.me/theorems/61d8fc34-5b07-40ba-a246-887ae263f671
-- title:
--   The multiplicative domain is an intersection of similarity images
-- statement:
--   Let $H=\mathbb C^I$, where $I$ is finite and nonempty. Let $\rho$ be a positive definite positive density matrix with ordinary trace one, and let $A\subseteq B(H)$ be a concrete unital star subalgebra sharing its identity. Let $E$ be the ordinary-trace-preserving conditional expectation onto $A$, and define $E_\rho(X)=E(\rho)^{-1/2}E(\rho^{1/2}X\rho^{1/2})E(\rho)^{-1/2}$. Its fixed points form $F_\rho$, and its multiplicative domain $N_\rho$ consists of all ambient $X$ satisfying both $E_\rho(X^*X)=E_\rho(X)^*E_\rho(X)$ and $E_\rho(XX^*)=E_\rho(X)E_\rho(X)^*$.
--
--   Then, as sets of all ambient matrices,
--
--   $$
--   N_\rho=\rho^{1/2}A\rho^{-1/2}\ \cap\ \rho^{-1/2}A\rho^{1/2}.
--   $$
--
--   This describes the whole multiplicative domain through two explicit similarities, including non-self-adjoint elements.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 4, Lemma 1: multiplicative domain as an intersection of similarities

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

/-- PDF pp.4--5, Lemma 1: the ambient multiplicative domain is the intersection
of the two similarity images. No restriction to self-adjoint elements is made. -/
theorem multiplicativeDomainSimilarities (A : Alg I) (rho : Mat I)
    (h : IsDensityMatrix rho) (hf : rho.PosDef) :
    (algebraMultiplicativeDomain Set.univ (generalizedExpectation A rho)) =
      ((fun X : Mat I => supportPower rho (1 / 2) * X * supportPower rho (-(1 / 2))) ''
        (A : Set (Mat I))) ∩
      ((fun X : Mat I => supportPower rho (-(1 / 2)) * X * supportPower rho (1 / 2)) ''
        (A : Set (Mat I))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
