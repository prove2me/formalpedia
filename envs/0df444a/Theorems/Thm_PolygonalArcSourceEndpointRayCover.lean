-- Prove2me | Theorems.Thm_PolygonalArcSourceEndpointRayCover
-- name    : PolygonalArcSourceEndpointRayCover
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:59.92398+00:00
-- url     : https://prove2.me/theorems/d786cf29-408d-4980-88e2-66d3f4cb0e73
-- title:
--   Polygonal Arc Source Endpoint Ray Cover
-- statement:
--   For every polygonal arc $\gamma$, there is a positive radius $r$
--   such that every point of $\gamma.carrier$ in $B(\gamma.source,r)$
--   lies on the ray from $\gamma.source$ through the second listed vertex:
--   $$
--     B(\gamma.source,r)\cap\gamma.carrier
--     \subseteq
--     \{\gamma.source+c(\gamma.vertices_1-\gamma.source):c\ge0\}.
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcSourceEndpointRayCover`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcSourceEndpointRayCover.lean#L1-L28

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcSourceEndpointRayCover (γ : PolygonalArc) :
    ∃ r : ℝ, 0 < r ∧
      (let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
       Metric.ball γ.source r ∩ γ.carrier ⊆
        {x | ∃ c : ℝ, 0 ≤ c ∧
          x = γ.source + c • (γ.vertices[1]'hfirst - γ.source)}) := by sorry
