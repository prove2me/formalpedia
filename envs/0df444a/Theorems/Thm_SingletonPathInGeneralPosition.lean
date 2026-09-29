-- Prove2me | Theorems.Thm_SingletonPathInGeneralPosition
-- name    : SingletonPathInGeneralPosition
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:20:21.428719+00:00
-- url     : https://prove2.me/theorems/57ce0484-7db1-4998-973c-539751407dcb
-- title:
--   Singleton polygonal path in general position
-- statement:
--   The theorem constructs a degenerate polygonal path consisting only of a point q outside a finite polygonal set K. Its source, target, and carrier are all q, and the path is in general position with respect to K.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/SingletonPathInGeneralPosition.lean#L1-L46

import Definitions.Def_PolygonalPathInGeneralPosition
open Classical
noncomputable section

lemma SingletonPathInGeneralPosition (K : FinitePolygonalSet)
    (q : EuclideanSpace ℝ (Fin 2)) (hq : q ∉ K.carrier) :
    ∃ γ : PolygonalPath,
      γ.source = q ∧ γ.target = q ∧
        γ.carrier = ({q} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          PolygonalPathInGeneralPosition γ K := by sorry
