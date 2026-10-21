-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_pebClosedConvex
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.pebClosedConvex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:50:09.759511+00:00
-- url     : https://prove2.me/theorems/50c97978-9185-4d8e-868c-f59902be829a
-- title:
--   Unnumbered: closedness and convexity of k-PEB channels
-- statement:
--   Let $H,H'$ be separable complex Hilbert spaces and $k\ge1$. A channel is $k$-partially entanglement breaking when its tensor product with the identity of every separable ancilla sends every density input into the continuous Schmidt class $S_k$. In the space $\mathcal F(H,H')$ of channels, equipped with pointwise trace-norm convergence on density inputs,
--
--   $$\mathcal P_k(H,H')\text{ is closed and convex}.$$
--
--   Thus the topology is strong channel convergence, and convexity uses real probabilistic mixtures of channels.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 10, Unnumbered: closedness and convexity of k-PEB channels

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF p.10, closedness and convexity of the k-PEB class.
Closedness is relative to channels in pointwise trace-norm topology. -/
theorem pebClosedConvex {I J : Type} [Countable I] [Countable J]
    (k : ℕ) (hk : 0 < k) :
    IsClosed {Phi : CanonicalChannel I J | isPEB k Phi} ∧ pebConvex I J k := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
