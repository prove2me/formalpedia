-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootIdentifyJumpAndResidueV2
-- name    : WeightedRootIntegralIdentity.weightedRootIdentifyJumpAndResidueV2
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T09:32:47.05262+00:00
-- url     : https://prove2.me/theorems/19201f44-f3b7-4ff1-aa89-13bb7fae5fdb
-- title:
--   Identify the bank jump with the concrete residue
-- statement:
--   The oriented bank jump equals the concrete residue-limit value under the accepted upper/lower boundary hypotheses.

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootJumpEqualsConcreteResidue
open Filter Topology

theorem WeightedRootIntegralIdentity.weightedRootIdentifyJumpAndResidueV2
    (U L : ℕ → ℂ) (A ρ : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A)))
    (hρ : Tendsto (fun m : ℕ => U m + L m) atTop (𝓝 ρ)) :
    A - starRingEnd ℂ A = ρ := by
  exact WeightedRootIntegralIdentity.weightedRootJumpEqualsConcreteResidue U L A ρ hU hL hρ
