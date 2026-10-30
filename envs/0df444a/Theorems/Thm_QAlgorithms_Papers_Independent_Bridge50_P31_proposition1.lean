-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_proposition1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.proposition1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:40:40.131884+00:00
-- url     : https://prove2.me/theorems/a504ff89-144f-4e2e-a750-591851d724a1
-- title:
--   Proposition 1
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   For a positive map $T:A\to B$,
--   $$
--   T\text{ is 2-positive}\quad\Longleftrightarrow\quad
--   \forall c\in A,\ c>0,\ \forall a\in A:\quad
--   \operatorname{ran}T(a)\subseteq\operatorname{ran}T(c),\quad
--   T(a^*c^{-1}a)\ge T(a)^*T(c)^+T(a).
--   $$
--   Here $c>0$ means positive invertible, and 2-positivity means positivity on all positive $2\times2$ operator blocks. The range guard is retained even when $T(c)$ is singular.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 5, Proposition 1

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

/-- PDF p.5, Proposition 1: every positive invertible reference, every input a. -/
theorem proposition1 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T) :
    AlgebraKPositive A T 2 ↔ ∀ c ∈ A, c.PosDef → GeneralizedSchwarz A T c := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
