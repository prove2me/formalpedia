-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:37:58.818544+00:00
-- url     : https://prove2.me/theorems/6277d5d6-11d9-4b74-9d2c-768e96b06563
-- title:
--   Lemma 1
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $T:A\to B$ be positive. The following are equivalent:
--   $$
--   \begin{gathered}
--   \text{$T(\omega)$ is invertible for every positive invertible $\omega\in A$};\\
--   \text{$T(\omega)$ is invertible for some positive invertible $\omega\in A$};\\
--    b\in B_+,\ T^*(b)=0\ \Longrightarrow\ b=0.
--   \end{gathered}
--   $$
--   Thus output faithfulness is characterized by faithfulness of the adjoint on the positive cone; trace preservation is unnecessary.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 3, Lemma 1

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

/-- PDF p.3, Lemma 1: all three conditions, with faithfulness on the positive cone. -/
theorem lemma1 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T) :
    List.TFAE [
      ∀ rho ∈ A, rho.PosDef → IsUnit (T rho),
      ∃ rho ∈ A, rho.PosDef ∧ IsUnit (T rho),
      FaithfulOn B (channelAdjoint T)] := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
