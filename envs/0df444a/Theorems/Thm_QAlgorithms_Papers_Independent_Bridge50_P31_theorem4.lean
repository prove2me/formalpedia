-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:47:10.940979+00:00
-- url     : https://prove2.me/theorems/a89d5b7a-f140-4561-863d-99b71d84edb3
-- title:
--   Theorem 4
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
--   The following six conditions are equivalent:
--
--   1. $T$ is reversible for $\mathcal S$.
--   2. $T^*(d(T(\sigma),\rho_0))=d(\sigma,\rho)$ for every $\sigma\in\mathcal S$.
--   3. $d(\sigma,\rho)\in F_\Phi$ for every $\sigma\in\mathcal S$.
--   4. Every real modular translate of every derivative belongs to the adjoint image of the multiplicative domain:
--   $$
--   \rho^{it}d(\sigma,\rho)\rho^{-it}\in T^*(M_{T^*}),\qquad\sigma\in\mathcal S,\ t\in\mathbb R.
--   $$
--   5. There is one CPTP map $\widehat R:B\to A$ with $\widehat R(T(\sigma))=\sigma$ for all $\sigma\in\mathcal S$.
--   6. There are CPTP maps $\widehat T:A\to B$ and $\widehat R:B\to A$ with $\widehat T(\sigma)=T(\sigma)$ and $\widehat R(T(\sigma))=\sigma$ simultaneously on the whole family.
--
--   These conditions characterize exact reversibility without assuming that $T$ itself is completely positive.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 13, Theorem 4

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

/-- PDF pp.13–14, Theorem 4: all SIX equivalent reversibility conditions,
including existence of CPTP replacements; these are conclusions, never premises. -/
theorem theorem4 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho) :
    List.TFAE [
      FamilyReversible A B T S,
      ∀ sigma ∈ S, channelAdjoint T (derivative (T sigma) (T rho)) = derivative sigma rho,
      ∀ sigma ∈ S, derivative sigma rho ∈ fixedPoints A (recoveryComposite T rho),
      ∀ sigma ∈ S, ∀ t : ℝ,
        cpow rho (Complex.I * (t : ℂ)) * derivative sigma rho * cpow rho (-Complex.I * (t : ℂ)) ∈
          channelAdjoint T '' algebraMultiplicativeDomain B (channelAdjoint T),
      ∃ R : MatrixMap J I, AlgebraChannel B A R ∧ ∀ sigma ∈ S, R (T sigma) = sigma,
      ∃ U : MatrixMap I J, ∃ R : MatrixMap J I, AlgebraChannel A B U ∧ AlgebraChannel B A R ∧
        ∀ sigma ∈ S, U sigma = T sigma ∧ R (T sigma) = sigma] := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
