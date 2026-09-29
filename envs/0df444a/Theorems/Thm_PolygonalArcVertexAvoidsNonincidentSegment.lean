-- Prove2me | Theorems.Thm_PolygonalArcVertexAvoidsNonincidentSegment
-- name    : PolygonalArcVertexAvoidsNonincidentSegment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:10:42.496813+00:00
-- url     : https://prove2.me/theorems/a3f1e939-b51b-4af0-aae3-e87d6146e5d2
-- title:
--   A polygonal-arc vertex avoids every nonincident segment
-- statement:
--   Let γ be a polygonal arc with vertices p₀, p₁, …, and let [pⱼ,pⱼ₊₁] be one of its listed segments. If the vertex index i is different from both j and j+1, then the vertex pᵢ does not belong to the closed segment [pⱼ,pⱼ₊₁]. The conclusion uses the defining properties of a polygonal arc: its listed vertices are pairwise distinct, and no vertex lies in the relative interior of a nonincident listed segment.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcVertexAvoidsNonincidentSegment.lean#L1-L33

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcVertexAvoidsNonincidentSegment (γ : PolygonalArc)
    {i j : ℕ} (hi : i < γ.vertices.length)
    (hj : j + 1 < γ.vertices.length) (hij : i ≠ j) (hijs : i ≠ j + 1) :
    γ.vertices[i] ∉ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by sorry
