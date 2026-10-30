-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:43:53.40967+00:00
-- url     : https://prove2.me/theorems/fda64f63-922e-4594-a216-3fa490abe7cb
-- title:
--   Theorem 1
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\Phi:A\to A$ be unital Schwarz and let $\rho$ be a faithful density with $\Phi^*(\rho)=\rho$. Write $F=\{a\in A:\Phi(a)=a\}$ and let $M_\Phi$ be the multiplicative domain defined by both Schwarz equalities. Then:
--
--   1. $F$ is a unital $*$-subalgebra contained in $M_\Phi$.
--   2. There is a conditional expectation $E:A\to F$ with $E^*(\rho)=\rho$.
--   3. $\rho^{it}F\rho^{-it}\subseteq F$ for every real $t$.
--   4. For every faithful trace $\tau$ on $F$, let $\rho^A\in F_+$ be the density of the restricted state: $\tau(a\rho^A)=\operatorname{Tr}(\rho a)$ for $a\in F$. Then
--   $$
--   \rho=\rho^A\rho^B,\qquad \rho^B\in F'\cap A,\quad\rho^B>0,\quad\Phi^*(\rho^B)=\rho^B.
--   $$
--   The factor $\rho^A$ is computed from the trace pairing, rather than supplied as extra data.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 7, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P31

open Filter MeasureTheory Set

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports matrixCommutant)

open QAlgorithms.Papers.Independent.Support50.P12
  (Alg AlgebraDensity AlgebraExtension PositiveOnConcreteAlgebra AlgebraTracePreserving
   AlgebraKPositive AlgebraCompletelyPositive supp spec cpow quasi hull modularSpec)

open QAlgorithms.Papers.Independent.Information100.P50 (OperatorMonotone)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF pp.7–8, Theorem 1: all four fixed-point conclusions. The restricted
state density is computed from the arbitrary faithful trace tau. -/
theorem theorem1 [Nonempty I] (A : Alg I) (Phi : MatrixMap I I)
    (hmap : AlgebraExtension A A Phi) (hschwarz : UnitalSchwarzOn A 1 1 Phi)
    (rho : Mat I) (hrho : AlgebraDensity A rho) (hfaith : rho.PosDef)
    (hinvariant : channelAdjoint Phi rho = rho) :
    let F := fixedPoints A Phi
    (IsStarAlgebraSet F ∧ F ⊆ algebraMultiplicativeDomain A Phi) ∧
    (∃ E : MatrixMap I I, ConditionalExpectation A F E ∧ channelAdjoint E rho = rho) ∧
    (∀ t : ℝ, ∀ a ∈ F,
      cpow rho (Complex.I * (t : ℂ)) * a * cpow rho (-Complex.I * (t : ℂ)) ∈ F) ∧
    (∀ tau : Mat I →ₗ[ℂ] ℂ, FaithfulTraceOn F tau →
      let rhoA := restrictionDensity F tau rho
      rhoA ∈ F ∧ rhoA.PosSemidef ∧ tau rhoA = 1 ∧
      (∀ a ∈ F, tau (a * rhoA) = (rho * a).trace) ∧
      ∃ rhoB ∈ A, rhoB ∈ matrixCommutant F ∧ rhoB.PosDef ∧
        channelAdjoint Phi rhoB = rhoB ∧ rho = rhoA * rhoB) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
