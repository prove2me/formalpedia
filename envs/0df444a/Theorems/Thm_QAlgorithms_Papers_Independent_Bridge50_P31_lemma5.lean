-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:45:13.453688+00:00
-- url     : https://prove2.me/theorems/5cf81034-e8ce-42a4-bf6f-b5726a25d58a
-- title:
--   Lemma 5
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\rho,\sigma$ be densities with $\operatorname{supp}\sigma\le\operatorname{supp}\rho$, and let $T$ be positive and trace preserving. For $d(\sigma,\rho)=\rho^{-1/2}\sigma\rho^{-1/2}$ and $T_\rho(a)=T(\rho)^{-1/2}T(\rho^{1/2}a\rho^{1/2})T(\rho)^{-1/2}$,
--   $$
--   d(T(\sigma),T(\rho))=T_\rho(d(\sigma,\rho)).
--   $$
--   The output support inclusion follows from positivity; it is not an additional hypothesis.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 12, Lemma 5

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

/-- PDF p.12, Lemma 5: derivative covariance under the computed forward state dual. -/
theorem lemma5 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T)
    (htp : AlgebraTracePreserving A T) (rho sigma : Mat I)
    (hrho : AlgebraDensity A rho) (hsigma : AlgebraDensity A sigma)
    (hsupp : Supports sigma rho) :
    derivative (T sigma) (T rho) = stateDual T rho (derivative sigma rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
