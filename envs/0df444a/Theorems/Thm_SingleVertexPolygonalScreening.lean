-- Prove2me | Theorems.Thm_SingleVertexPolygonalScreening
-- name    : SingleVertexPolygonalScreening
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:20:25.95572+00:00
-- url     : https://prove2.me/theorems/3bd0a8e6-48b4-415d-b346-dc1afb1f876b
-- title:
--   Single-vertex polygonal screening
-- statement:
--   Given a point a outside a finite polygonal set K and a nonempty open set W, there is a point x in W outside K such that the segment from a to x avoids every listed point and has neither a nontrivial common subsegment nor a parallel interior crossing with any listed segment of K.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/SingleVertexPolygonalScreening.lean#L1-L161

import Definitions.Def_FinitePolygonalSet
open Classical
noncomputable section

lemma SingleVertexPolygonalScreening
    (K : FinitePolygonalSet) (a : EuclideanSpace ℝ (Fin 2))
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (ha : a ∉ K.carrier) (hWopen : IsOpen W) (hWnonempty : W.Nonempty) :
    ∃ x ∈ W, x ∉ K.carrier ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∉ segment ℝ a x) ∧
      (∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), s ∈ K.segments →
          ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
            segment ℝ p q ⊆ segment ℝ a x ∩ segment ℝ s.1 s.2) ∧
      (∀ (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), s ∈ K.segments →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ openSegment ℝ a x → p ∈ openSegment ℝ s.1 s.2 →
            ¬ ∃ c : ℝ, s.2 - s.1 = c • (x - a)) := by sorry
