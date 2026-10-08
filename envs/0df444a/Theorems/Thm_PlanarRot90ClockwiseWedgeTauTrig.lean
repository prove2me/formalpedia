-- Prove2me | Theorems.Thm_PlanarRot90ClockwiseWedgeTauTrig
-- name    : PlanarRot90ClockwiseWedgeTauTrig
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:46.318895+00:00
-- url     : https://prove2.me/theorems/4a3ec4c2-873f-4ef4-8354-be7551a4a533
-- title:
--   Planar Rot90 Clockwise Wedge Tau Trig
-- statement:
--   Fix a base angle $\beta$.  For any $x\ne\beta$, write
--   $$
--     \tau(x)=
--     \begin{cases}
--       \beta-x, & x<\beta,\\
--       \beta-x+2\pi, & x>\beta.
--     \end{cases}
--   $$
--   Then for $\alpha\ne\beta$ and $\nu\ne\beta$,
--   $$
--    \sin(\alpha-\beta)=-\sin \tau(\alpha),\qquad
--    \cos(\alpha-\beta)=\cos \tau(\alpha),
--   $$
--   and
--   $$
--    \sin(\alpha-\nu)=\sin(\tau(\nu)-\tau(\alpha)).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarRot90ClockwiseWedgeTauTrig`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90ClockwiseWedgeTauTrig.lean#L1-L59

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma PlanarRot90ClockwiseWedgeTauTrig (β ν α : ℝ)
    (hαν : α ≠ β) (hνβ : ν ≠ β) :
    let τ : ℝ → ℝ :=
      fun x => if x = β then 2 * Real.pi
        else if x < β then β - x
        else β - x + 2 * Real.pi
    Real.sin (α - β) = -Real.sin (τ α) ∧
      Real.cos (α - β) = Real.cos (τ α) ∧
      Real.sin (α - ν) = Real.sin (τ ν - τ α) := by sorry
