-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootFinalWeightedRootIdentity
-- name    : WeightedRootIntegralIdentity.weightedRootFinalWeightedRootIdentity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T09:37:50.930014+00:00
-- url     : https://prove2.me/theorems/8b346a98-4f4f-41b3-b51d-64baf14bffff
-- title:
--   Final weighted-root integral identity
-- statement:
--   After inserting the accepted evaluations of the origin derivative and reciprocal product, the normalized contour balance yields the weighted-root integral identity and its finite weighted geometric-mean expression.

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootInstantiateNormalizedAlgebra
open scoped BigOperators

theorem WeightedRootIntegralIdentity.weightedRootFinalWeightedRootIdentity
    (n : ℕ) (a w : ℕ → ℝ) (J : ℝ)
    (hbalance : 2 * J = 2 * Real.pi *
      ((∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)))) :
    J / Real.pi =
      (∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
  exact WeightedRootIntegralIdentity.weightedRootInstantiateNormalizedAlgebra n a w J hbalance
