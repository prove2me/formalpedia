-- Prove2me | Theorems.Thm_UnitCirclesIntersectionsAtMostTwo
-- name    : UnitCirclesIntersectionsAtMostTwo
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:17.042775+00:00
-- url     : https://prove2.me/theorems/6e5897e1-35a5-4073-889c-59d6c35414bc
-- title:
--   Unit Circles Intersections At Most Two
-- statement:
--   If $a,b\in\mathbb{R}^2$ are distinct, then the two unit circles centered at $a$ and $b$ have a finite intersection and meet in at most two points.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCirclesIntersectionsAtMostTwo`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCirclesIntersectionsAtMostTwo.lean#L1-L229

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_UnitCircle

open Classical
noncomputable section

lemma UnitCirclesIntersectionsAtMostTwo (a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b) :
    {x : EuclideanSpace ℝ (Fin 2) | x ∈ UnitCircle a ∧ x ∈ UnitCircle b}.Finite ∧
      ({x : EuclideanSpace ℝ (Fin 2) | x ∈ UnitCircle a ∧ x ∈ UnitCircle b}.ncard) ≤ 2 := by sorry
