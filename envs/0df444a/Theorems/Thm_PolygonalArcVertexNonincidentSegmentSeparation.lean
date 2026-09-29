-- Prove2me | Theorems.Thm_PolygonalArcVertexNonincidentSegmentSeparation
-- name    : PolygonalArcVertexNonincidentSegmentSeparation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:12:21.640542+00:00
-- url     : https://prove2.me/theorems/9e85fb71-3417-4966-b209-b50c598453a1
-- title:
--   Positive separation of a vertex from a nonincident polygonal-arc segment
-- statement:
--   Let γ be a polygonal arc. For a listed vertex pᵢ and a listed segment [pⱼ,pⱼ₊₁] with i different from both j and j+1, there is a strictly positive number δ such that every point q on that segment remains at distance at least δ from pᵢ:
--
--   $$
--   \exists\,\delta>0\quad\text{such that}\quad
--   q\in[p_j,p_{j+1}]\Longrightarrow\delta\le d(p_i,q).
--   $$
--
--   Thus a nonincident vertex and segment have a positive clearance, not merely disjoint carriers. This is the quantitative separation used to choose uniform collar-control radii around the vertices.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcVertexNonincidentSegmentSeparation.lean#L1-L43

import Definitions.Def_PolygonalArc
import Mathlib.Analysis.Normed.Module.Convex

open Classical
noncomputable section

lemma PolygonalArcVertexNonincidentSegmentSeparation (γ : PolygonalArc)
    {i j : ℕ} (hi : i < γ.vertices.length)
    (hj : j + 1 < γ.vertices.length) (hij : i ≠ j) (hijs : i ≠ j + 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q, q ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] →
        δ ≤ dist γ.vertices[i] q := by sorry
