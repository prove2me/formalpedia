-- Prove2me | Theorems.Thm_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_parallelogram
-- name    : Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.parallelogram
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:27.43538+00:00
-- url     : https://prove2.me/theorems/7a154efe-b286-41ed-b29f-fa5b91443e80
-- title:
--   A plane whose unit ball has at most four extreme points is $\ell_\infty^2$
-- statement:
--   Let $V$ be a real normed space of dimension $2$ whose closed unit ball has at most four extreme points.
--   Then there are $a,b\in V$ with $$\|sa+tb\|=\max(|s|,|t|)\qquad(s,t\in\mathbb R),$$ so $V$ is linearly isometric to $\ell_\infty^2$ and its ball is a parallelogram.
-- source:
--   This repository: claim CUB109 (claims/cub.md), expositions/c0_planes_with_scalars.md §4 (every real plane is a non-parallelogram plane or isometric to ℓ∞²)

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two
theorem parallelogram {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2)
    (hext : (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard ≤ 4) :
    ∃ a b : V, ∀ s t : ℝ, ‖s • a + t • b‖ = max |s| |t| := by sorry
end Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two
