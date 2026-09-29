-- Prove2me | Theorems.Thm_PolygonalArcVertexMemCarrier
-- name    : PolygonalArcVertexMemCarrier
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:36:17.093856+00:00
-- url     : https://prove2.me/theorems/7eace5cd-3365-43b9-9cf0-c85a43e2d04d
-- title:
--   Vertices of a polygonal arc lie on its carrier
-- statement:
--   For a polygonal arc $\Gamma$, every point appearing in its finite vertex list belongs to the arc's carrier. Thus each polygonal vertex is contained in one of the segments making up the carrier. This elementary structural fact lets endpoint and vertex membership be converted into carrier membership in later geometric arguments.
--
--   **Formalization Note** The vertex list is represented as a Lean `List`, while membership in the carrier is membership in the set defined by the arc's segment decomposition.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcVertexMemCarrier.lean#L1-L34

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcVertexMemCarrier (Γ : PolygonalArc)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ Γ.vertices) : p ∈ Γ.carrier := by sorry
