-- Prove2me | Theorems.Thm_PlanarRot90CoefficientUniqueness
-- name    : PlanarRot90CoefficientUniqueness
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:46:05.287391+00:00
-- url     : https://prove2.me/theorems/44b4d79b-ec4c-4ab6-b671-0198cf37d56d
-- title:
--   Coefficient uniqueness in the planar quarter-turn basis
-- statement:
--   For a nonzero planar direction $d$, if a vector $v$ is represented as $a d+b\,\operatorname{PlanarRot90}(d)$, then the coefficients are recovered by the two normalized inner products with $d$ and its quarter-turn.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90CoefficientUniqueness.lean#L1-L29

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90CoefficientUniqueness {d v : EuclideanSpace ℝ (Fin 2)}
    (hd : d ≠ 0) {a b : ℝ}
    (h : v = a • d + b • PlanarRot90 d) :
    a = inner ℝ v d / (‖d‖ ^ 2) ∧
      b = inner ℝ v (PlanarRot90 d) / (‖d‖ ^ 2) := by sorry
