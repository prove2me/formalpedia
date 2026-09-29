-- Prove2me | Theorems.Thm_PolygonalArcFinitePolygonalSet
-- name    : PolygonalArcFinitePolygonalSet
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:08:28.38387+00:00
-- url     : https://prove2.me/theorems/ee3c3ea2-14a2-428d-b00b-30360809dde9
-- title:
--   Finite polygonal set realizing a polygonal arc
-- statement:
--   Every polygonal arc in the plane is the carrier of a finite polygonal set. In other words, for each polygonal arc Γ there is a finite collection of marked points and nondegenerate line segments whose union, together with the marked points, is exactly Γ.carrier, and whose listed segments record all segment intersections as marked points. This finite representation packages the arc in the data structure used for subsequent perturbation and intersection arguments.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcFinitePolygonalSet.lean#L1-L127

import Definitions.Def_FinitePolygonalSet
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcFinitePolygonalSet (Γ : PolygonalArc) :
    ∃ K : FinitePolygonalSet, K.carrier = Γ.carrier := by sorry
