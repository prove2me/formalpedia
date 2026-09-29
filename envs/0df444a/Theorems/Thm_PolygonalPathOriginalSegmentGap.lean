-- Prove2me | Theorems.Thm_PolygonalPathOriginalSegmentGap
-- name    : PolygonalPathOriginalSegmentGap
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:38.27298+00:00
-- url     : https://prove2.me/theorems/1756c1d1-ab4e-4f77-8b2c-aca92e17b45c
-- title:
--   Polygonal path original segment gap
-- statement:
--   A subsegment of an original polygonal path segment that is disjoint from a forbidden set can be replaced by a polygonal path whose carrier avoids the forbidden set and a prescribed set avoided by the original path.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathOriginalSegmentGap.lean#L1-L37

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathOriginalSegmentGap
    (K F : Set (EuclideanSpace ℝ (Fin 2))) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length)
    (p q : EuclideanSpace ℝ (Fin 2)) :
    α.carrier ⊆ Kᶜ →
      segment ℝ p q ⊆ segment ℝ α.vertices[i] α.vertices[i + 1] →
        Disjoint (segment ℝ p q) F →
          ∃ η : PolygonalPath,
            η.source = p ∧
              η.target = q ∧
                η.carrier ⊆ (K ∪ F)ᶜ := by sorry
