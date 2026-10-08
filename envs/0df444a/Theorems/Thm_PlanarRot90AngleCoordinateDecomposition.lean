-- Prove2me | Theorems.Thm_PlanarRot90AngleCoordinateDecomposition
-- name    : PlanarRot90AngleCoordinateDecomposition
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:40.512501+00:00
-- url     : https://prove2.me/theorems/5baa824b-76cb-4e01-aadf-305dbdcc7b62
-- title:
--   Planar Rot90 Angle Coordinate Decomposition
-- statement:
--   Let
--   $$
--     e(t)=(\cos t,\sin t)\in\mathbb R^2.
--   $$
--   If $r_b\ne0$, then the vector $r_a e(\alpha)$ has coordinates in the
--   ordered frame $(r_b e(\beta),\operatorname{rot}_{90}(r_b e(\beta)))$
--   given by
--   $$
--     x={r_a\over r_b}\cos(\alpha-\beta),\qquad
--     y={r_a\over r_b}\sin(\alpha-\beta).
--   $$
--   That is,
--   $$
--     r_a e(\alpha)
--     =x\,r_b e(\beta)+y\,\operatorname{rot}_{90}(r_b e(\beta)),
--   $$
--   and these two coordinates $x,y$ are unique.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarRot90AngleCoordinateDecomposition`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90AngleCoordinateDecomposition.lean#L1-L71

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90AngleCoordinateDecomposition (β α rb ra : ℝ) (hrb : rb ≠ 0) :
    let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun t => WithLp.toLp 2
        (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
    let base : EuclideanSpace ℝ (Fin 2) := rb • e β
    let x : ℝ := (ra / rb) * Real.cos (α - β)
    let y : ℝ := (ra / rb) * Real.sin (α - β)
    ra • e α = x • base + y • PlanarRot90 base ∧
      ∀ {x' y' : ℝ},
        ra • e α = x' • base + y' • PlanarRot90 base →
          x' = x ∧ y' = y := by sorry
