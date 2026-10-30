-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma9
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:50:45.824879+00:00
-- url     : https://prove2.me/theorems/917d207b-c048-4786-aa59-4bfca47f7378
-- title:
--   Lemma 9
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\rho,\sigma$ be densities with $\rho$ invertible. For every real $t$ let $P_{t,+}$ be the projection onto the strictly positive spectrum of $\sigma-t\rho$, and let $P_{t,0}$ be its kernel projection. At every $t\ge0$,
--   $$
--   \lim_{s\to t^+}P_{s,+}=P_{t,+},\qquad
--   \lim_{s\to t^-}P_{s,+}=P_{t,+}+P_{t,0}.
--   $$
--   Limits are in operator norm. Defining the projections also for negative parameters makes the left limit at zero meaningful.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 17, Lemma 9

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

/-- PDF pp.17–18, Lemma 9: right continuity and the left limit including the
kernel. The functions are defined on all real parameters, including left of zero.
The finite-dimensional matrix topology is the operator-norm topology. -/
theorem lemma9 [Nonempty I] (A : Alg I) (rho sigma : Mat I)
    (hrho : AlgebraDensity A rho) (hsigma : AlgebraDensity A sigma) (hfaith : rho.PosDef) :
    ∀ t : ℝ, 0 ≤ t →
      Tendsto (positiveTest sigma rho) (𝓝[>] t) (𝓝 (positiveTest sigma rho t)) ∧
      Tendsto (positiveTest sigma rho) (𝓝[<] t)
        (𝓝 (positiveTest sigma rho t + kernelTest sigma rho t)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
