-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_relative_entropy_mixture_lower
-- name    : QAlgorithms.Papers.Independent.Support50.P18.relative_entropy_mixture_lower
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:23:52.794824+00:00
-- url     : https://prove2.me/theorems/070ac1af-a6b9-43c9-93e6-a5f1b5532f87
-- title:
--   Lemma 3: lower mixture inequality for infinite-dimensional relative entropy
-- statement:
--   Let $\rho,\sigma,\omega$ be normalized states on any separable complex Hilbert space, let $0<p<1$, and let $D$ denote extended quantum relative entropy in nats. Then
--
--   $$pD(\rho\|\omega)+(1-p)D(\sigma\|\omega)\le D(p\rho+(1-p)\sigma\|\omega)+h_2(p).$$
--
--   All relative entropies may be infinite. This additive form is equivalent to (36) and avoids subtracting from infinity. No support or entropy-finiteness condition is imposed.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 13, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-- Lemma 3, PDF pp.13--14: the additive h2 form covers infinite values on
both sides. No finite entropy, common support or full-rank premise is imposed. -/
theorem relative_entropy_mixture_lower {I : Type} [Countable I]
    (rho sigma omega : State I) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ENNReal.ofReal p * extendedRelativeEntropyNats rho.coefficients omega.coefficients +
      ENNReal.ofReal (1 - p) * extendedRelativeEntropyNats sigma.coefficients omega.coefficients ≤
    extendedRelativeEntropyNats
      (convexOperatorMixture p rho.coefficients sigma.coefficients) omega.coefficients +
      ENNReal.ofReal (Real.binEntropy p) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
