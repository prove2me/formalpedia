-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma11
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:54:24.881978+00:00
-- url     : https://prove2.me/theorems/9fe5f51f-047b-4a23-98c8-2b3b0e7cdbf7
-- title:
--   Lemma 11
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Assume $T^*:B\to A$ is unital Schwarz, $\rho$ a faithful density, and $T(\rho)$ faithful. For arbitrary $x\in A$ and $s\ge0$, put $J_\rho^s=sR_\rho+L_\rho$, where $L_\rho(a)=\rho a$ and $R_\rho(a)=a\rho$. Then
--   $$
--   \operatorname{Tr}x^*(J_\rho^s)^{-1}(x)\ge
--   \operatorname{Tr}T(x)^*(J_{T(\rho)}^s)^{-1}(T(x)),
--   $$
--   and equality holds exactly when
--   $$
--   (J_\rho^s)^{-1}(x)=T^*((J_{T(\rho)}^s)^{-1}(T(x))).
--   $$
--   No self-adjointness or tangent-space assumption on $x$, or Schwarz assumption on $T_\rho$, is added.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 23, Lemma 11

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

/-- PDF pp.23–24, Lemma 11: arbitrary x (not necessarily tangent), only the
adjoint Schwarz premise, the inequality AND its exact equality condition. -/
theorem lemma11 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hadj : UnitalSchwarzOn B 1 1 (channelAdjoint T))
    (rho : Mat I) (hrho : AlgebraDensity A rho) (hfaith : rho.PosDef)
    (hout : (T rho).PosDef) (x : Mat I) (hx : x ∈ A) (s : ℝ) (hs : 0 ≤ s) :
    tr ((T x)ᴴ * resolvent (T rho) (T rho) s (T x)) ≤
      tr (xᴴ * resolvent rho rho s x) ∧
    ((tr (xᴴ * resolvent rho rho s x) = tr ((T x)ᴴ * resolvent (T rho) (T rho) s (T x))) ↔
      resolvent rho rho s x = channelAdjoint T (resolvent (T rho) (T rho) s (T x))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
