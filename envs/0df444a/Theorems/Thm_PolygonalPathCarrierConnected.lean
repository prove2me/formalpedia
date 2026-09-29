-- Prove2me | Theorems.Thm_PolygonalPathCarrierConnected
-- name    : PolygonalPathCarrierConnected
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:34:26.282378+00:00
-- url     : https://prove2.me/theorems/f1b43e19-3b5d-4107-aaf4-5af1916c2611
-- title:
--   Connectedness of a polygonal path carrier
-- statement:
--   For every polygonal path in the Euclidean plane, the path carrier is connected. The carrier consists of the path's endpoints together with the line segments joining consecutive vertices, so this lemma provides the connectedness fact needed when a polygonal path meets an open cover.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathCarrierConnected.lean#L1-L101

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathCarrierConnected]

lemma PolygonalPathCarrierConnected (γ : PolygonalPath) : IsConnected γ.carrier := by sorry
