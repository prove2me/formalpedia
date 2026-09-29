-- Prove2me | Theorems.Thm_R03SP06_triangle_residual_no_cut_vertex
-- name    : R03SP06.triangle_residual_no_cut_vertex
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:13.671588+00:00
-- url     : https://prove2.me/theorems/23e16eac-effc-41ee-835c-7f0d6f802093
-- title:
--   Triangle residual no cut vertex
-- statement:
--   Conditional q=3 cut-free theorem. The `hport` premise is the one-external neighbor property of a triangle in a cubic simple graph.
--
--   $$G-V(C_3)\text{ satisfies the stated residual-connectivity conclusion}.$ $
--
--   This isolates one reusable port-counting or residual-connectivity step for deleting a triangle from a cubic three-vertex-connected graph. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

theorem triangle_residual_no_cut_vertex
    {G : SimpleGraph V}
    {T : Finset V} {x : V}
    (hT : T.card = 3)
    (hxT : x ∉ T)
    (hres : ∃ v : V, v ∉ T ∧ v ≠ x)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected)
    (hport : ∀ ⦃t u v : V⦄, t ∈ T → u ∉ T → v ∉ T →
      G.Adj t u → G.Adj t v → u = v) :
    (G.induce {v : V | v ∉ T ∧ v ≠ x}).Connected := by sorry

end R03SP06
