-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma6
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:46:25.926217+00:00
-- url     : https://prove2.me/theorems/f0f45c53-75a7-4769-9cc4-e0ccb6e2d4b5
-- title:
--   Lemma 6
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\rho$ be a faithful density, $\sigma$ any density, and $T$ positive and trace preserving. Define the support-aware recovery
--   $R_\rho(b)=\rho^{1/2}T^*(T(\rho)^{-1/2}bT(\rho)^{-1/2})\rho^{1/2}$ and $d(\sigma,\rho)=\rho^{-1/2}\sigma\rho^{-1/2}$. Then
--   $$
--   R_\rho(T(\sigma))=\sigma\quad\Longleftrightarrow\quad
--   T^*(d(T(\sigma),T(\rho)))=d(\sigma,\rho).
--   $$
--   This identifies recovery by the adjoint dual even when the output has proper support.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 12, Lemma 6

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

/-- PDF pp.12–13, Lemma 6: the adjoint dual is the support-aware Petz formula;
no faithfulness of the output is required. -/
theorem lemma6 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T)
    (htp : AlgebraTracePreserving A T) (rho sigma : Mat I)
    (hrho : AlgebraDensity A rho) (hsigma : AlgebraDensity A sigma) (hfaith : rho.PosDef) :
    petz rho T (T sigma) = sigma ↔
      channelAdjoint T (derivative (T sigma) (T rho)) = derivative sigma rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
