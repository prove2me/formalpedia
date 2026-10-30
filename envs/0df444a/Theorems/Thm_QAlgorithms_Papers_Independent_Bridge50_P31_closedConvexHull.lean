-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_closedConvexHull
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.closedConvexHull
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:00:30.750991+00:00
-- url     : https://prove2.me/theorems/faeb40bb-43fc-4f4b-bc15-f2f39eb3596b
-- title:
--   §3 unnumbered: closed-convex-hull invariance
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be any set of densities, possibly empty, and assume only that $T^*$ is unital Schwarz. Then
--   $$
--   T\text{ is reversible for }\mathcal S\quad\Longleftrightarrow\quad
--   T\text{ is reversible for }\overline{\operatorname{co}}_{\mathbb R}(\mathcal S).
--   $$
--   In both cases one common linear recovery with unital Schwarz adjoint must recover every member. No faithful reference state is required for this reduction.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 9, §3 unnumbered: closed-convex-hull invariance

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

/-- PDF p.9: one common recovery works on S exactly when it works on its
closed REAL convex hull. No faithful reference state is needed. -/
theorem closedConvexHull [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (T : MatrixMap I J) (hmap : AlgebraExtension A B T)
    (hadj : UnitalSchwarzOn B 1 1 (channelAdjoint T))
    (S : Set (Mat I)) (hstates : ∀ sigma ∈ S, AlgebraDensity A sigma) :
    FamilyReversible A B T S ↔ FamilyReversible A B T (hull S) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
