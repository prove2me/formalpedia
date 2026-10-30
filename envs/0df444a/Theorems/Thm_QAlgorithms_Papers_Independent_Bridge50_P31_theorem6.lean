-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem6
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:52:40.331096+00:00
-- url     : https://prove2.me/theorems/a5ec9391-bd2b-4c2c-8d81-81f38d7ab9b3
-- title:
--   Theorem 6
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a set of density operators in $A$ containing an invertible $\rho$, with $\rho_0=T(\rho)$ invertible. Assume $T^*$ and the computed map
--   $$
--   T_\rho(a)=\rho_0^{-1/2}T(\rho^{1/2}a\rho^{1/2})\rho_0^{-1/2}
--   $$
--   are unital Schwarz maps. Reversibility means that one linear map $R:B\to A$, whose adjoint is unital Schwarz, satisfies $R(T(\sigma))=\sigma$ for every $\sigma\in\mathcal S$.
--
--   Let $\widetilde{\mathcal S}=\{\rho^{is}\sigma\rho^{-is}:\sigma\in\mathcal S,s\in\mathbb R\}$, and write the norm criterion on a family $\mathcal C$ as
--   $$
--   \|\sigma-t\rho\|_1=\|T(\sigma)-tT(\rho)\|_1,\qquad\sigma\in\mathcal C,\ t\ge0.
--   $$
--   Then:
--
--   1. Reversibility for $\mathcal S$ is equivalent to this criterion on $\widetilde{\mathcal S}$.
--   2. If $\widetilde{\mathcal S}\subseteq\mathcal S$, it is equivalent to the criterion on $\mathcal S$ itself.
--   3. If $B$ is abelian, it is equivalent to the criterion on $\mathcal S$; when these equivalent conditions hold, all pairs of states in $\mathcal S$ commute.
--   4. If every state in $\mathcal S$ commutes with $\rho$, it is equivalent to the criterion on $\mathcal S$.
--
--   No general unsaturated criterion is asserted outside these regimes.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 19, Theorem 6

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

/-- PDF pp.19–20, Theorem 6: all four regimes. In the abelian-output case,
pairwise commutation follows WHEN the norm criterion (equivalently reversibility) holds. -/
theorem theorem6 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho) :
    (FamilyReversible A B T S ↔ NormCriterion T rho (saturation rho S)) ∧
    ((saturation rho S ⊆ S) → (FamilyReversible A B T S ↔ NormCriterion T rho S)) ∧
    ((∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      (FamilyReversible A B T S ↔ NormCriterion T rho S) ∧
      (NormCriterion T rho S → ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)) ∧
    ((∀ sigma ∈ S, sigma * rho = rho * sigma) →
      (FamilyReversible A B T S ↔ NormCriterion T rho S)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
