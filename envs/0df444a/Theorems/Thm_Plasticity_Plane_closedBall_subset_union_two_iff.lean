-- Prove2me | Theorems.Thm_Plasticity_Plane_closedBall_subset_union_two_iff
-- name    : Plasticity.Plane.closedBall_subset_union_two_iff
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:28.181721+00:00
-- url     : https://prove2.me/theorems/38960d3b-146f-43e7-9c39-f52fd86f8ce6
-- title:
--   Two translates of the unit ball of a plane cover it exactly when they are opposite short multiples of an edge vector
-- statement:
--   Let $V$ be a real normed space of dimension $2$ with closed unit ball $D$, and let $u,v\in V$ be nonzero.
--   Then $D\subseteq(u+D)\cup(v+D)$, where $u+D$ and $v+D$ are the closed unit balls about $u$ and $v$, if and only if there are a functional $f$ of norm $1$, points $a,b\in D$ with $f(a)=f(b)=1$, and reals $t,s>0$ with $t+s\le1$ such that $$u=t(b-a),\qquad v=-s(b-a).$$
--   The points $a,b$ lie on the face $\{y\in D:f(y)=1\}$ but need not be its endpoints.
-- source:
--   This repository: claim CUB99(1) (claims/cub.md), proof in expositions/c0_one_general_plane.md §2.2

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem closedBall_subset_union_two_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    Metric.closedBall (0 : V) 1 ⊆ Metric.closedBall u 1 ∪ Metric.closedBall v 1 ↔
      ∃ f : StrongDual ℝ V, ‖f‖ = 1 ∧ ∃ a b : V, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ f a = 1 ∧ f b = 1 ∧
        ∃ t s : ℝ, 0 < t ∧ 0 < s ∧ t + s ≤ 1 ∧ u = t • (b - a) ∧ v = -(s • (b - a)) := by sorry
end Plasticity.Plane
