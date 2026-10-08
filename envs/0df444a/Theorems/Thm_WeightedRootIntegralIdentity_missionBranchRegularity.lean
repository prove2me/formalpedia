-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_missionBranchRegularity
-- name    : WeightedRootIntegralIdentity.missionBranchRegularity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T10:48:53.605713+00:00
-- url     : https://prove2.me/theorems/882de3ca-320a-4496-b892-14d9cee2bea3
-- title:
--   Continuity on the branch-safe domain
-- statement:
--   A differentiable branch integrand on the slit contour domain is continuous there, hence continuous on each finite contour piece.

import Mathlib

theorem WeightedRootIntegralIdentity.missionBranchRegularity
    (F : ℂ → ℂ) (D : Set ℂ)
    (hF : DifferentiableOn ℂ F D) :
    ContinuousOn F D := by sorry
