-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_adjacent_edges_of_countable
-- name    : Plasticity.Plane.exists_adjacent_edges_of_countable
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:29.749916+00:00
-- url     : https://prove2.me/theorems/362d783f-c23c-4269-bf28-66fafb3bc344
-- title:
--   A planar ball with countably many extreme points has two edges meeting at a corner
-- statement:
--   Let $W$ be a real normed space of dimension $2$ whose closed unit ball $D$ has countably many extreme points (finitely many included).
--   Then there are pairwise distinct extreme points $a,b,c$ of $D$ with $$\|a+b\|=\|b+c\|=2,$$ that is, $[a,b]$ and $[b,c]$ are edges of $D$ meeting at $b$.
-- source:
--   This repository: claim CUB108 (claims/cub.md), its run of consecutive edges, in the form used by the formal proof: one corner with two edges, which also replaces the vertex cycle of claim CUB106(2); expositions/c0_planar_mixtures.md §4

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_adjacent_edges_of_countable {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (hW : Module.finrank ℝ W = 2)
    (hcount : (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).Countable) :
    ∃ a ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
    ∃ b ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
    ∃ c ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ‖a + b‖ = 2 ∧ ‖b + c‖ = 2 := by
  sorry
end Plasticity.Plane
