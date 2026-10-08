-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_finiteKeyholeLimitAssembly
-- name    : WeightedRootIntegralIdentity.finiteKeyholeLimitAssembly
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T11:16:40.085102+00:00
-- url     : https://prove2.me/theorems/ffc79492-9d66-43d8-ad9e-d39ef4f3526a
-- title:
--   Finite keyhole limit assembly
-- statement:
--   The bank jump follows from the upper and lower boundary limits together with convergence of the finite contour bank sums to the residue value.

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootJumpEqualsConcreteResidue
open Filter Topology

theorem WeightedRootIntegralIdentity.finiteKeyholeLimitAssembly
    (U L : ℕ → ℂ) (A ρ : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A)))
    (hres : Tendsto (fun m : ℕ => U m + L m) atTop (𝓝 ρ)) :
    A - starRingEnd ℂ A = ρ := by sorry
