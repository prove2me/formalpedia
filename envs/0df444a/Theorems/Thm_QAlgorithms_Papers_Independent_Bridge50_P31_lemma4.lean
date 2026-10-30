-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:41:31.372346+00:00
-- url     : https://prove2.me/theorems/1df04249-3e34-4170-bfb0-400544998b4b
-- title:
--   Lemma 4
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $T$ be positive and trace preserving and $\rho$ an invertible density operator. Set $p_0=\operatorname{supp}T(\rho)$ and define $T_\rho(a)=T(\rho)^{-1/2}T(\rho^{1/2}a\rho^{1/2})T(\rho)^{-1/2}$ as a map $A\to p_0Bp_0$. Then
--   $$
--   T_\rho\text{ is Schwarz}\quad\Longleftrightarrow\quad
--   \forall a\in A:\ \operatorname{ran}T(a)\subseteq\operatorname{ran}T(\rho),\quad
--   T(a^*\rho^{-1}a)\ge T(a)^*T(\rho)^+T(a).
--   $$
--   The output need not be faithful; the Schwarz property is tested in its actual support corner.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 6, Lemma 4

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

/-- PDF p.6, Lemma 4: the computed dual has its actual support-corner codomain.
Invertibility of T(rho) is not assumed. -/
theorem lemma4 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T)
    (htp : AlgebraTracePreserving A T) (rho : Mat I)
    (hrho : AlgebraDensity A rho) (hfaith : rho.PosDef) :
    SchwarzOn A (stateDual T rho) ↔ GeneralizedSchwarz A T rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
