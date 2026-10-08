-- Prove2me | Theorems.Thm_PlanarRot90ClockwiseWedgeSignCriterion
-- name    : PlanarRot90ClockwiseWedgeSignCriterion
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:37.728238+00:00
-- url     : https://prove2.me/theorems/ac4cfb04-bb60-4f8c-ab85-e082e4f0afc9
-- title:
--   Planar Rot90 Clockwise Wedge Sign Criterion
-- statement:
--   Let $A,N\in(0,2\pi)$.  Then the following three sign descriptions are
--   equivalent to the single interval condition $A<N$:
--   $$
--   \begin{cases}
--   A<\pi\text{ and }\sin(N-A)>0, & \sin N>0,\\
--   A<\pi\text{ or }\sin(N-A)>0, & \sin N<0,\\
--   A<\pi, & \sin N=0.
--   \end{cases}
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarRot90ClockwiseWedgeSignCriterion`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90ClockwiseWedgeSignCriterion.lean#L1-L110

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma PlanarRot90ClockwiseWedgeSignCriterion (A N : ℝ)
    (hA0 : 0 < A) (hA2 : A < 2 * Real.pi)
    (hN0 : 0 < N) (hN2 : N < 2 * Real.pi) :
    (if 0 < Real.sin N then
      A < Real.pi ∧ 0 < Real.sin (N - A)
     else if Real.sin N < 0 then
      A < Real.pi ∨ 0 < Real.sin (N - A)
     else
      A < Real.pi) ↔ A < N := by sorry
