-- Prove2me | Theorems.Thm_PolygonalPathFiniteOccurrenceLocalCuts
-- name    : PolygonalPathFiniteOccurrenceLocalCuts
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:20.002824+00:00
-- url     : https://prove2.me/theorems/0f243108-5206-4f0f-ae42-7a0322ad6a0f
-- title:
--   Finite local cuts around path--set occurrences
-- statement:
--   Let \(F\) meet the carrier of a polygonal path in finitely many points, let \(U\) be open around every interior occurrence, and assume all path vertices avoid \(F\). Then there are before/after cut maps for every occurrence such that each short segment meets \(F\) only at that occurrence, distinct occurrence segments are disjoint, and every point of a path segment lying in \(F\) lies on one of the short segments.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathFiniteOccurrenceLocalCuts.lean#L1-484

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

set_option maxHeartbeats 1200000

lemma PolygonalPathFiniteOccurrenceLocalCuts
    (α : PolygonalPath) (F U : Set (EuclideanSpace ℝ (Fin 2))) :
    Set.Finite (α.carrier ∩ F) →
      IsOpen U →
        (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
            (x : EuclideanSpace ℝ (Fin 2)),
            x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
              x ∈ F → x ∈ U) →
          (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ F) →
            ∃ (cutBefore cutAfter :
                ∀ (i : ℕ), i + 1 < α.vertices.length →
                  EuclideanSpace ℝ (Fin 2) →
                    EuclideanSpace ℝ (Fin 2)),
              (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                  (x : EuclideanSpace ℝ (Fin 2)),
                  x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                    x ∈ F →
                      cutBefore i hi x ∈ openSegment ℝ α.vertices[i] x ∧
                        cutAfter i hi x ∈ openSegment ℝ x α.vertices[i + 1] ∧
                          cutBefore i hi x ∈ U \ F ∧
                            cutAfter i hi x ∈ U \ F ∧
                              segment ℝ (cutBefore i hi x) (cutAfter i hi x) ∩ F =
                                {x}) ∧
                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                    (x y : EuclideanSpace ℝ (Fin 2)),
                    x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                      y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                        x ∈ F →
                          y ∈ F →
                            x ≠ y →
                              Disjoint
                                (segment ℝ (cutBefore i hi x) (cutAfter i hi x))
                                (segment ℝ (cutBefore i hi y) (cutAfter i hi y))) ∧
                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                    (y : EuclideanSpace ℝ (Fin 2)),
                    y ∈ segment ℝ α.vertices[i] α.vertices[i + 1] →
                      y ∈ F →
                        ∃ x : EuclideanSpace ℝ (Fin 2),
                          x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧
                            x ∈ F ∧
                              y ∈ segment ℝ (cutBefore i hi x)
                                (cutAfter i hi x)) := by sorry
