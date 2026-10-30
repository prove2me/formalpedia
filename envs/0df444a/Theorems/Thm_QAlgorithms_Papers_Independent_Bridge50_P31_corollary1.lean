-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_corollary1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.corollary1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:48:22.145918+00:00
-- url     : https://prove2.me/theorems/87452145-c570-4e11-836b-d2502b8873e7
-- title:
--   Corollary 1
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a set of density operators in $A$ containing an invertible $\rho$, with $\rho_0=T(\rho)$ invertible. Assume $T^*$ and the computed map
--   $$
--   T_\rho(a)=\rho_0^{-1/2}T(\rho^{1/2}a\rho^{1/2})\rho_0^{-1/2}
--   $$
--   are unital Schwarz maps. Reversibility means that one linear map $R:B\to A$, whose adjoint is unital Schwarz, satisfies $R(T(\sigma))=\sigma$ for every $\sigma\in\mathcal S$.
--
--   Define the modular saturation as the union
--   $$
--   \widetilde{\mathcal S}=\{\rho^{it}\sigma\rho^{-it}:\sigma\in\mathcal S,\ t\in\mathbb R\}.
--   $$
--   Then $T$ is reversible for $\mathcal S$ if and only if it is reversible for $\widetilde{\mathcal S}$. The same definition of one common recovery is used for both families.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 14, Corollary 1

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

/-- PDF p.14, Corollary 1: reversibility is unchanged by modular saturation. -/
theorem corollary1 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho) :
    FamilyReversible A B T S ↔ FamilyReversible A B T (saturation rho S) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
