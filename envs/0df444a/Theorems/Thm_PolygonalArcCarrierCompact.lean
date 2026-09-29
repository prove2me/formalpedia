-- Prove2me | Theorems.Thm_PolygonalArcCarrierCompact
-- name    : PolygonalArcCarrierCompact
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:59:44.513182+00:00
-- url     : https://prove2.me/theorems/2c98ac57-1e19-44e2-98e6-1acced813298
-- title:
--   Compactness of the carrier of a polygonal arc
-- statement:
--   For every polygonal arc γ, its carrier—the finite union of the closed line segments joining consecutive vertices—is a compact subset of the Euclidean plane. This compactness is the structural finiteness input used to cut away a neighborhood of an endpoint while retaining a compact arc tail.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCarrierCompact.lean#L1-32

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcCarrierCompact (γ : PolygonalArc) : IsCompact γ.carrier := by sorry
