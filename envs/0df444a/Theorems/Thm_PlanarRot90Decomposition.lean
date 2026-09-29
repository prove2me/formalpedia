-- Prove2me | Theorems.Thm_PlanarRot90Decomposition
-- name    : PlanarRot90Decomposition
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:46:02.052362+00:00
-- url     : https://prove2.me/theorems/11acf99c-0212-4941-8a44-e0dff0b08ab5
-- title:
--   Orthogonal decomposition in the planar quarter-turn basis
-- statement:
--   Every vector in the Euclidean plane decomposes, relative to a nonzero direction $d$, into its component along $d$ and its component along $\operatorname{PlanarRot90}(d)$, with coefficients given by normalized inner products.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90Decomposition.lean#L1-L69

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90Decomposition (d v : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) :
    v =
      (inner ℝ v d / (‖d‖ ^ 2)) • d +
        (inner ℝ v (PlanarRot90 d) / (‖d‖ ^ 2)) • PlanarRot90 d := by sorry
