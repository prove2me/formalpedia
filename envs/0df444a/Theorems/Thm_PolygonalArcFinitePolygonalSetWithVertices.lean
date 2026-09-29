-- Prove2me | Theorems.Thm_PolygonalArcFinitePolygonalSetWithVertices
-- name    : PolygonalArcFinitePolygonalSetWithVertices
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:57:14.544329+00:00
-- url     : https://prove2.me/theorems/fac89018-ea02-475e-935f-fd7a62f284c4
-- title:
--   Finite polygonal set with all arc vertices listed
-- statement:
--   For every polygonal arc Γ in the plane, there is a finite polygonal set K whose carrier is exactly the carrier of Γ and whose marked point set contains every vertex of Γ. Thus the arc can be represented by finite polygonal data while retaining all of its vertices as listed points.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcFinitePolygonalSetWithVertices.lean#L1-L12

import Definitions.Def_FinitePolygonalSet
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcFinitePolygonalSetWithVertices (Γ : PolygonalArc) :
    ∃ K : FinitePolygonalSet,
      K.carrier = Γ.carrier ∧
        ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ Γ.vertices → v ∈ K.points := by sorry
