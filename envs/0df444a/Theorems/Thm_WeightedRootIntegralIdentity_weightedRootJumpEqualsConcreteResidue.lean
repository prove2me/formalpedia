-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootJumpEqualsConcreteResidue
-- name    : WeightedRootIntegralIdentity.weightedRootJumpEqualsConcreteResidue
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T06:24:43.189784+00:00
-- url     : https://prove2.me/theorems/46e85f48-e46d-49ae-a5dc-e56b099cad72
-- title:
--   Bank jump equals the concrete residue balance
-- statement:
--   If the upper and lower banks converge with the orientation-correct conjugacy relation, and the same finite bank sum converges by the concrete Cauchy/residue balance to R, then the real-axis jump A minus its conjugate equals R.
-- source:
--   Uniqueness of limits applied to the oriented bank-sum sequence, combining the accepted jump-limit and concrete residue theorems.

import Mathlib
open Filter Topology
namespace WeightedRootIntegralIdentity
theorem weightedRootJumpEqualsConcreteResidue
    (U L : ℕ → ℂ) (A R : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A)))
    (hres : Tendsto (fun m : ℕ => U m + L m) atTop (𝓝 R)) :
    A - starRingEnd ℂ A = R := by sorry
end WeightedRootIntegralIdentity
