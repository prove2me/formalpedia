-- Prove2me | Theorems.Thm_PlanarNormalizedAngleRepresentation
-- name    : PlanarNormalizedAngleRepresentation
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:19.299075+00:00
-- url     : https://prove2.me/theorems/5b6d0a4c-f862-4203-af57-2b8e01049fcb
-- title:
--   Planar Normalized Angle Representation
-- statement:
--   Every nonzero vector $v=(v_0,v_1)\in\mathbb R^2$ has a normalized polar
--   angle $\alpha\in[0,2\pi)$ and a positive radius $r$ such that
--   $$
--     v=r(\cos\alpha,\sin\alpha).
--   $$
--   The angle is obtained from the complex argument of $v_0+iv_1$, adding
--   $2\pi$ if the argument is negative.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarNormalizedAngleRepresentation`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarNormalizedAngleRepresentation.lean#L1-L67

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma PlanarNormalizedAngleRepresentation (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) :
    let z : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I
    let α : ℝ := let a := Complex.arg z
      if 0 ≤ a then a else a + 2 * Real.pi
    0 ≤ α ∧ α < 2 * Real.pi ∧
      ∃ r : ℝ, 0 < r ∧
        v = r • WithLp.toLp 2
          (fun k : Fin 2 => if k = 0 then Real.cos α else Real.sin α) := by sorry
