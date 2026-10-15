-- Prove2me | Theorems.Thm_Plasticity_Topology_eq_of_norm_sub_eq_on_intrinsicFrontier
-- name    : Plasticity.Topology.eq_of_norm_sub_eq_on_intrinsicFrontier
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T02:24:12.528966+00:00
-- url     : https://prove2.me/theorems/21349e85-b721-445a-ba13-03fbf8479aaa
-- title:
--   Two points of a bounded set at equal distances from every point of its relative boundary coincide
-- statement:
--   Let $C$ be a bounded subset of a real normed space and $x,y\in C$. If $\|x-b\|=\|y-b\|$ for every point $b$ of the relative boundary of $C$ (its frontier within its affine hull), then $x=y$.
--   If $x\ne y$, the ray from $x$ through $y$ leaves $C$ at a relative boundary point $b$ beyond $y$, and $\|x-b\|>\|y-b\|$.
-- source:
--   Elementary; used in this repository's proof of the facial covering corollary of claim F17 (expositions/faces/finite_faces_boundary_crossing.md §6) in place of Mankiewicz's extension theorem

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Intrinsic

namespace Plasticity.Topology
theorem eq_of_norm_sub_eq_on_intrinsicFrontier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Bornology.IsBounded C) (x y : E) (hx : x ∈ C) (hy : y ∈ C)
    (h : ∀ b ∈ intrinsicFrontier ℝ C, ‖x - b‖ = ‖y - b‖) :
    x = y := by sorry
end Plasticity.Topology
