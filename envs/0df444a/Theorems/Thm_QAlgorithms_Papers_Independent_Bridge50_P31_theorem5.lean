-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:49:21.336173+00:00
-- url     : https://prove2.me/theorems/43e65176-1b74-47cf-ac99-c5a8969a7ddd
-- title:
--   Theorem 5
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a set of density operators in $A$ containing an invertible $\rho$, with $\rho_0=T(\rho)$ invertible. Assume $T^*$ and the computed map
--   $$
--   T_\rho(a)=\rho_0^{-1/2}T(\rho^{1/2}a\rho^{1/2})\rho_0^{-1/2}
--   $$
--   are unital Schwarz maps. Reversibility means that one linear map $R:B\to A$, whose adjoint is unital Schwarz, satisfies $R(T(\sigma))=\sigma$ for every $\sigma\in\mathcal S$.
--
--   Write $d(\sigma,\rho)=\rho^{-1/2}\sigma\rho^{-1/2}$, $\Phi=T^*T_\rho$, and $\widetilde\Phi=T_\rho T^*$. For a map $U$, $F_U$ is its fixed-point set in its domain algebra, and $M_U$ consists of elements satisfying both $U(a^*a)=U(a)^*U(a)$ and $U(aa^*)=U(a)U(a)^*$.
--
--   The following four conditions are equivalent:
--
--   1. $T$ is reversible for $\mathcal S$.
--   2. There is one positive invertible $\rho^B\in F_\Phi'\cap A$ such that every $\sigma\in\mathcal S$ admits a positive $\sigma_0^A\in F_{\widetilde\Phi}$ with
--   $$
--   \sigma=T^*(\sigma_0^A)\rho^B,\qquad T(\sigma)=\sigma_0^A T(\rho^B).
--   $$
--   3. The same two identities hold with one common $\rho^B\in A_+$ and positive $\sigma_0^A\in B$, without initially requiring invertibility or fixed-point membership.
--   4. There is one common $\rho^B\in A_+$ such that each $\sigma\in\mathcal S$ has $\sigma=\sigma^A\rho^B$ for a positive $\sigma^A\in T^*(M_{T^*})$.
--
--   Every common factor is chosen before quantifying over the states; the weaker-looking criteria retain the strength of reversibility.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 14, Theorem 5

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

/-- PDF pp.14–15, Theorem 5: all four factorization criteria, with ONE common
positive factor chosen before every sigma. Both identities remain in (ii),(iii). -/
theorem theorem5 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho) :
    List.TFAE [
      FamilyReversible A B T S,
      ∃ rhoB ∈ A, rhoB.PosDef ∧ rhoB ∈ matrixCommutant (fixedPoints A (recoveryComposite T rho)) ∧
        ∀ sigma ∈ S, ∃ sigma0A ∈ fixedPoints B (phiTilde T rho), sigma0A.PosSemidef ∧
          sigma = channelAdjoint T sigma0A * rhoB ∧ T sigma = sigma0A * T rhoB,
      ∃ rhoB ∈ A, rhoB.PosSemidef ∧
        ∀ sigma ∈ S, ∃ sigma0A ∈ B, sigma0A.PosSemidef ∧
          sigma = channelAdjoint T sigma0A * rhoB ∧ T sigma = sigma0A * T rhoB,
      ∃ rhoB ∈ A, rhoB.PosSemidef ∧
        ∀ sigma ∈ S, ∃ sigmaA ∈ channelAdjoint T '' algebraMultiplicativeDomain B (channelAdjoint T),
          sigmaA.PosSemidef ∧ sigma = sigmaA * rhoB] := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
