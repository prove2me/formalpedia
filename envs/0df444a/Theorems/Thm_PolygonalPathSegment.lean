-- Prove2me | Theorems.Thm_PolygonalPathSegment
-- name    : PolygonalPathSegment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:19:11.280986+00:00
-- url     : https://prove2.me/theorems/3a4e43cd-8d43-4173-8f08-9f32b0a060cb
-- title:
--   Straight segment as a polygonal path
-- statement:
--   For any two points $p$ and $q$ in the Euclidean plane, the straight segment from $p$ to $q$ is the carrier of a polygonal path with source $p$ and target $q$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathSegment.lean#L1-L40

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathSegment
    (p q : EuclideanSpace ℝ (Fin 2)) :
    ∃ γ : PolygonalPath,
      γ.source = p ∧
        γ.target = q ∧
          γ.carrier = segment ℝ p q := by sorry
