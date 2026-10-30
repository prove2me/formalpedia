-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem7
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:53:29.109365+00:00
-- url     : https://prove2.me/theorems/d3147d54-f56d-413b-b3ea-bb7b02104b90
-- title:
--   Theorem 7
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a set of density operators in $A$ containing an invertible $\rho$, with $\rho_0=T(\rho)$ invertible. Assume $T^*$ and the computed map
--   $$
--   T_\rho(a)=\rho_0^{-1/2}T(\rho^{1/2}a\rho^{1/2})\rho_0^{-1/2}
--   $$
--   are unital Schwarz maps. Reversibility means that one linear map $R:B\to A$, whose adjoint is unital Schwarz, satisfies $R(T(\sigma))=\sigma$ for every $\sigma\in\mathcal S$.
--
--   Write $\overline{\operatorname{co}}$ for closed real convex hull. Let $C(\sigma,\rho)=-\log\inf_{0\le u\le1}\operatorname{Tr}\sigma^u\rho^{1-u}$, using support projections at exponent zero, and let $H_r(\sigma,\rho)=\sup_{0\le u<1}[-ur-\log\operatorname{Tr}\sigma^u\rho^{1-u}]/(1-u)$ for $r>0$, with $H_0(\sigma,\rho)=D(\sigma\Vert\rho)$. Reversibility is equivalent to each of:
--
--   1. $C(\sigma,\rho)=C(T(\sigma),T(\rho))$ for every $\sigma\in\overline{\operatorname{co}}(\mathcal S)$.
--   2. For every $\sigma\in\mathcal S$, $t\ge0$ and integer $n\ge1$,
--   $$
--   \|\sigma^{\otimes n}-t\rho^{\otimes n}\|_1=
--   \|T(\sigma)^{\otimes n}-tT(\rho)^{\otimes n}\|_1.
--   $$
--   3. $H_r(\sigma,\rho)=H_r(T(\sigma),T(\rho))$ for every $\sigma\in\mathcal S$ and $r\ge0$.
--
--   Moreover, if $\mathcal S_0\subseteq\mathcal S$, $\mathcal S\subseteq\overline{\operatorname{co}}(\mathcal S_0\cup\{\rho\})$ and $T(\rho)\notin\overline{T(\mathcal S_0)}$, there exists $r_0>0$ such that reversibility is equivalent to existence of one $r\in[0,r_0]$ for which Hoeffding equality holds for every $\sigma\in\overline{\operatorname{co}}(\mathcal S)$. This includes the trivial empty auxiliary-family case.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 21, Theorem 7

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

/-- PDF pp.21–22, Theorem 7: four equivalences and the extra common-rate
criterion. Closed hulls and the excluded OUTPUT CLOSURE are retained; an empty
S0 causes no empty real infimum because r0 is existential here. -/
theorem theorem7 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho) :
    List.TFAE [
      FamilyReversible A B T S,
      ∀ sigma ∈ hull S,
        QAlgorithms.Papers.Independent.Support50.P12.chernoff sigma rho =
          QAlgorithms.Papers.Independent.Support50.P12.chernoff (T sigma) (T rho),
      ∀ sigma ∈ S, ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
        QAlgorithms.traceNorm (copies n sigma - (t : ℂ) • copies n rho) =
          QAlgorithms.traceNorm (copies n (T sigma) - (t : ℂ) • copies n (T rho)),
      ∀ sigma ∈ S, ∀ r : ℝ, 0 ≤ r → QAlgorithms.Papers.Independent.Support50.P12.hoeffding sigma rho r = QAlgorithms.Papers.Independent.Support50.P12.hoeffding (T sigma) (T rho) r] ∧
    (∀ S0 : Set (Mat I), S0 ⊆ S → S ⊆ hull (S0 ∪ {rho}) → T rho ∉ closure (T '' S0) →
      ∃ r0 : ℝ, 0 < r0 ∧
        (FamilyReversible A B T S ↔ ∃ r ∈ Icc (0 : ℝ) r0, ∀ sigma ∈ hull S,
          QAlgorithms.Papers.Independent.Support50.P12.hoeffding sigma rho r = QAlgorithms.Papers.Independent.Support50.P12.hoeffding (T sigma) (T rho) r)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
