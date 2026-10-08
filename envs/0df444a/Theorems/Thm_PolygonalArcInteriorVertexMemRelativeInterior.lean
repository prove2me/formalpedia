-- Prove2me | Theorems.Thm_PolygonalArcInteriorVertexMemRelativeInterior
-- name    : PolygonalArcInteriorVertexMemRelativeInterior
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:37.742034+00:00
-- url     : https://prove2.me/theorems/c39a830b-9d39-4f05-bb9c-1012d1af4f47
-- title:
--   Polygonal Arc Interior Vertex Mem Relative Interior
-- statement:
--   Let $\gamma$ be a polygonal arc with listed vertices
--   $p_0,\ldots,p_m$.  If $i$ is a listed vertex index with
--   $0<i$ and $i+1<m+1$, then
--   $$
--     p_i\in\gamma.\operatorname{relativeInterior}.
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcInteriorVertexMemRelativeInterior`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInteriorVertexMemRelativeInterior.lean#L1-L45

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcInteriorVertexMemRelativeInterior (γ : PolygonalArc)
    (i : Fin γ.vertices.length) (hpos : 0 < i.1)
    (hnext : i.1 + 1 < γ.vertices.length) :
    γ.vertices[i.1] ∈ γ.relativeInterior := by sorry
