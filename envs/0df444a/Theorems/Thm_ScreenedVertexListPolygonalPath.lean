-- Prove2me | Theorems.Thm_ScreenedVertexListPolygonalPath
-- name    : ScreenedVertexListPolygonalPath
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:20:34.210174+00:00
-- url     : https://prove2.me/theorems/3eb5af6c-83b8-4d1a-94e4-520a7057f33b
-- title:
--   Screened vertex-list polygonal path
-- statement:
--   A nonempty screened vertex list determines a polygonal path with exactly those vertices, the prescribed source and target, and the carrier given by its endpoints and consecutive segments. The resulting path is in general position with respect to the finite polygonal set K.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ScreenedVertexListPolygonalPath.lean#L1-L133

import Definitions.Def_PolygonalPathInGeneralPosition
open Classical
noncomputable section

lemma ScreenedVertexListPolygonalPath (K : FinitePolygonalSet)
    (xs : List (EuclideanSpace ℝ (Fin 2)))
    (source target : EuclideanSpace ℝ (Fin 2))
    (hxs : xs ≠ [])
    (hsource : xs.head? = some source)
    (htarget : xs.getLast? = some target)
    (hsourceK : source ∉ K.carrier)
    (htargetK : target ∉ K.carrier)
    (hvertices : ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ xs → v ∉ K.carrier)
    (hpoints : ∀ (i : ℕ) (hi : i + 1 < xs.length)
      (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ K.points → p ∉ segment ℝ xs[i] xs[i + 1])
    (hoverlap : ∀ (i : ℕ) (hi : i + 1 < xs.length)
      (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      s ∈ K.segments →
        ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
          segment ℝ p q ⊆ segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2)
    (htransverse : ∀ (i : ℕ) (hi : i + 1 < xs.length)
      (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
      (_hs : s ∈ K.segments) (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ openSegment ℝ xs[i] xs[i + 1] →
        p ∈ openSegment ℝ s.1 s.2 →
          ¬ ∃ c : ℝ, s.2 - s.1 = c • (xs[i + 1] - xs[i])) :
    ∃ γ : PolygonalPath,
      γ.vertices = xs ∧
        γ.source = source ∧
          γ.target = target ∧
            γ.carrier =
              ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                {p | ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                  p ∈ segment ℝ xs[i] xs[i + 1]} ∧
              PolygonalPathInGeneralPosition γ K := by sorry
