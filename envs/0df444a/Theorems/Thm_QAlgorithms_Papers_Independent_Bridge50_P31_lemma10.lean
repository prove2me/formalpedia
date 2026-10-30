-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma10
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:51:41.947358+00:00
-- url     : https://prove2.me/theorems/3e8b6201-6ee3-4449-946b-f122e8515a8b
-- title:
--   Lemma 10
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $T$ be positive and trace preserving, and let $\rho,\sigma$ be densities with $\rho$ and $T(\rho)$ invertible. Define $P_{t,+},P_{t,0}$ for $\sigma-t\rho$ and $Q_{t,+},Q_{t,0}$ for $T(\sigma)-tT(\rho)$ using strictly positive and zero spectral subspaces. Then
--   $$
--   \begin{aligned}
--   &\forall t\in\mathbb R,\quad\|T(\sigma)-tT(\rho)\|_1=\|\sigma-t\rho\|_1\\
--   &\quad\Longleftrightarrow\quad
--   \forall t\in\mathbb R,\quad P_{t,+}=T^*(Q_{t,+}),\quad P_{t,0}=T^*(Q_{t,0}).
--   \end{aligned}
--   $$
--   The kernel ties are part of the equivalence, and the trace norm has no factor one half.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 19, Lemma 10

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

/-- PDF p.19, Lemma 10: all REAL thresholds and BOTH pulled-back spectral projections. -/
theorem lemma10 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T)
    (htp : AlgebraTracePreserving A T) (rho sigma : Mat I)
    (hrho : AlgebraDensity A rho) (hsigma : AlgebraDensity A sigma)
    (hfaith : rho.PosDef) (hout : (T rho).PosDef) :
    (∀ t : ℝ, QAlgorithms.traceNorm (T sigma - (t : ℂ) • T rho) =
      QAlgorithms.traceNorm (sigma - (t : ℂ) • rho)) ↔
    (∀ t : ℝ, positiveTest sigma rho t = channelAdjoint T (positiveTest (T sigma) (T rho) t) ∧
      kernelTest sigma rho t = channelAdjoint T (kernelTest (T sigma) (T rho) t)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
