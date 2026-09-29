-- Prove2me | Theorems.Thm_PolygonalPathExtendSegment
-- name    : PolygonalPathExtendSegment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:19:12.536984+00:00
-- url     : https://prove2.me/theorems/24c663c1-9768-417e-9090-4b94b4590648
-- title:
--   Extending a polygonal path by a segment
-- statement:
--   Let $\gamma$ be a polygonal path in a set $S$, and let the straight segment from its target to a point $z$ also lie in $S$. Then one can append that segment to obtain a polygonal path from the original source to $z$ whose carrier remains contained in $S$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathExtendSegment.lean#L1-L107

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathExtendSegment
    (S : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath)
    (z : EuclideanSpace ℝ (Fin 2)) :
    γ.carrier ⊆ S →
      segment ℝ γ.target z ⊆ S →
        ∃ η : PolygonalPath,
          η.source = γ.source ∧
            η.target = z ∧
              η.carrier ⊆ S := by sorry
