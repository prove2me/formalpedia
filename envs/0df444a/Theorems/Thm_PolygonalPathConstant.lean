-- Prove2me | Theorems.Thm_PolygonalPathConstant
-- name    : PolygonalPathConstant
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:19:08.607595+00:00
-- url     : https://prove2.me/theorems/f092e035-286d-43e6-8ea2-160b41d095b3
-- title:
--   Constant polygonal path
-- statement:
--   For every point $p$ in the Euclidean plane, there is a polygonal path whose source and target are both $p$ and whose carrier is exactly the singleton $\{p\}$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathConstant.lean#L1-L24

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathConstant (p : EuclideanSpace ℝ (Fin 2)) :
    ∃ γ : PolygonalPath,
      γ.source = p ∧
        γ.target = p ∧
          γ.carrier = ({p} : Set (EuclideanSpace ℝ (Fin 2))) := by sorry
