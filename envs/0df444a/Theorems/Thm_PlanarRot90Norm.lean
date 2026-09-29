-- Prove2me | Theorems.Thm_PlanarRot90Norm
-- name    : PlanarRot90Norm
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:46:08.516013+00:00
-- url     : https://prove2.me/theorems/b4663ea2-9052-4879-bccc-4cb66ba62a8c
-- title:
--   The planar quarter-turn preserves norm
-- statement:
--   The planar quarter-turn operator preserves Euclidean norm: $\|\operatorname{PlanarRot90}(d)\|=\|d\|$ for every planar vector $d$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90Norm.lean#L1-L15

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90Norm (d : EuclideanSpace ℝ (Fin 2)) :
    ‖PlanarRot90 d‖ = ‖d‖ := by sorry
