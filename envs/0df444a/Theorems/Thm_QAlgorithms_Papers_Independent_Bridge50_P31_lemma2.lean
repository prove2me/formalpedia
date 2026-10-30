-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:38:47.098313+00:00
-- url     : https://prove2.me/theorems/d3257414-1b2e-405f-b904-b126673ba957
-- title:
--   Lemma 2
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $T$ be positive with $T^*(I)\le I$, and let $\rho,\sigma\in A_+$, without any trace normalization. Set $p=\operatorname{supp}\rho$, $p_0=\operatorname{supp}T(\rho)$, $q=\operatorname{supp}\sigma$, and $q_0=\operatorname{supp}T(\sigma)$. Then
--   $$
--   T^*(I-p_0)\le I-p,\qquad q\le p\Rightarrow q_0\le p_0,\qquad T(pAp)\subseteq p_0Bp_0.
--   $$
--   If $T^*(I)=I$, also $T^*(p_0)\ge p$. These clauses control how a positive map transports support corners.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 3, Lemma 2

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

/-- PDF pp.3–4, Lemma 2: support transport, corner transport and the unital addendum. -/
theorem lemma2 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T)
    (hsub : LE (channelAdjoint T 1) 1)
    (rho sigma : Mat I) (hrho : rho ∈ A) (hrhop : rho.PosSemidef)
    (hsigma : sigma ∈ A) (hsigmap : sigma.PosSemidef) :
    let p := supp rho
    let p0 := supp (T rho)
    LE (channelAdjoint T (1 - p0)) (1 - p) ∧
    (LE (supp sigma) p → LE (supp (T sigma)) p0) ∧
    (∀ a ∈ supportCorner A p, T a ∈ supportCorner B p0) ∧
    (channelAdjoint T 1 = 1 → LE p (channelAdjoint T p0)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
