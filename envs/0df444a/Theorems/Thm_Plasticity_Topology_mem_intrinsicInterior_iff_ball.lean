-- Prove2me | Theorems.Thm_Plasticity_Topology_mem_intrinsicInterior_iff_ball
-- name    : Plasticity.Topology.mem_intrinsicInterior_iff_ball
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:53.672275+00:00
-- url     : https://prove2.me/theorems/fd641f9a-457f-445b-add2-e3b12d34f9fc
-- title:
--   A point of a set lies in its relative interior iff a small ball of its direction space around the point stays in the set
-- statement:
--   Let $C$ be a subset of a real normed space and $x$ a point of the space. Then $x$ lies in the relative interior of $C$ (its interior within the affine hull) if and only if there is $\varepsilon>0$ with $x+w\in C$ for every $w$ in the linear span of $C-C$ with $\|w\|<\varepsilon$.
-- source:
--   Elementary; Mathlib's intrinsicInterior

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Intrinsic

namespace Plasticity.Topology
theorem mem_intrinsicInterior_iff_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (x : E) :
    x ∈ intrinsicInterior ℝ C ↔ ∃ ε > 0, ∀ w ∈ vectorSpan ℝ C, ‖w‖ < ε → x + w ∈ C := by sorry
end Plasticity.Topology
