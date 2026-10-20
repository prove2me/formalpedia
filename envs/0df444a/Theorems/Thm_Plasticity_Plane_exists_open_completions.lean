-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_open_completions
-- name    : Plasticity.Plane.exists_open_completions
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:27.384019+00:00
-- url     : https://prove2.me/theorems/3f5b8781-e169-4013-bcc6-d31e8e790f71
-- title:
--   Near a good direction of a plane, the completions of a ball centre contain a nonempty open set
-- statement:
--   Let $V$ be a real normed space of dimension $2$ with closed unit ball $D$, let $e\in V$ with $\|e\|=1$, and let $p\ne q$ be extreme points of $D$ with $\|p-e\|<1$ and $\|q-e\|<1$ (so $e$ is a *good* direction).
--   Then for every $s$ with $0<s\le1$ there is a nonempty open set $U\subseteq V\times V$ such that every $(c_1,c_2)\in U$ satisfies $c_1\ne0$, $c_2\ne0$, $\|c_1\|\le1$, $\|c_2\|\le1$ and $$D\subseteq B(se,1)\cup B(c_1,1)\cup B(c_2,1),$$ where $B(c,1)$ is the closed ball of radius $1$ about $c$.
--   Such pairs $(c_1,c_2)$ are the *completions* of $se$.
-- source:
--   This repository: claim CUB102(1) (claims/cub.md), proof in expositions/c0_planes_front.md §2.1, which reruns the completions argument of claim CUB99(2) in expositions/c0_one_general_plane.md §2.3

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_open_completions {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (e p q : V) (he : ‖e‖ = 1)
    (hp : p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    (hq : q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) (hpq : p ≠ q)
    (hpe : ‖p - e‖ < 1) (hqe : ‖q - e‖ < 1) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ U : Set (V × V), IsOpen U ∧ U.Nonempty ∧ ∀ c ∈ U, c.1 ≠ 0 ∧ c.2 ≠ 0 ∧
      ‖c.1‖ ≤ 1 ∧ ‖c.2‖ ≤ 1 ∧
      Metric.closedBall (0 : V) 1 ⊆
        Metric.closedBall (s • e) 1 ∪ Metric.closedBall c.1 1 ∪ Metric.closedBall c.2 1 := by sorry
end Plasticity.Plane
