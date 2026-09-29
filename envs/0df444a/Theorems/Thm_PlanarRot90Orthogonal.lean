-- Prove2me | Theorems.Thm_PlanarRot90Orthogonal
-- name    : PlanarRot90Orthogonal
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:46:14.534981+00:00
-- url     : https://prove2.me/theorems/3ae07ffb-88cf-4221-840c-a3b5e6e5f86c
-- title:
--   Orthogonality of the planar quarter-turn
-- statement:
--   A planar vector is orthogonal to its quarter-turn: $\langle d,\operatorname{PlanarRot90}(d)angle=0$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90Orthogonal.lean#L1-L14

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90Orthogonal (d : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ d (PlanarRot90 d) = 0 := by sorry
