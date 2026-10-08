-- Prove2me | Theorems.Thm_PlanarRot90ClockwiseWedgeAngleCriterion
-- name    : PlanarRot90ClockwiseWedgeAngleCriterion
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:50.377914+00:00
-- url     : https://prove2.me/theorems/d477c67a-6ba8-4a8e-9d80-29cd96a0ce9a
-- title:
--   Planar Rot90 Clockwise Wedge Angle Criterion
-- statement:
--   Let $e(t)=(\cos t,\sin t)$, let
--   $\beta,\nu,\alpha\in[0,2\pi)$ with $\alpha\ne\beta$ and
--   $\nu\ne\beta$, and let $r_b,r_\nu,r_\alpha>0$.  Put
--   $$
--     b=r_b e(\beta),\qquad v=r_\nu e(\nu),\qquad w=r_\alpha e(\alpha).
--   $$
--   Suppose
--   $$
--     w=x b+y\operatorname{rot}_{90}(b),\qquad
--     v=c b-s\operatorname{rot}_{90}(b).
--   $$
--   For $t\ne\beta$, write
--   $$
--     \tau(t)=
--     \begin{cases}
--       \beta-t, & t<\beta,\\
--       \beta-t+2\pi, & t>\beta.
--     \end{cases}
--   $$
--   Then the displayed wedge sign condition
--   $$
--   \begin{cases}
--   y<0\text{ and }cy+sx>0, & s>0,\\
--   y<0\text{ or }cy+sx>0, & s<0,\\
--   y<0, & s=0,
--   \end{cases}
--   $$
--   is equivalent to $\tau(\alpha)<\tau(\nu)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarRot90ClockwiseWedgeAngleCriterion`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90ClockwiseWedgeAngleCriterion.lean#L1-L209

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

lemma PlanarRot90ClockwiseWedgeAngleCriterion
    (β ν α rb rn ra c s x y : ℝ)
    (hβ0 : 0 ≤ β) (hβ2 : β < 2 * Real.pi)
    (hν0 : 0 ≤ ν) (hν2 : ν < 2 * Real.pi)
    (hα0 : 0 ≤ α) (hα2 : α < 2 * Real.pi)
    (hrb : 0 < rb) (hrn : 0 < rn) (hra : 0 < ra)
    (hαν : α ≠ β) (hνβ : ν ≠ β)
    (hpoint :
      let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
        fun t => WithLp.toLp 2
          (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
      let base : EuclideanSpace ℝ (Fin 2) := rb • e β
      ra • e α = x • base + y • PlanarRot90 base)
    (hother :
      let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
        fun t => WithLp.toLp 2
          (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
      let base : EuclideanSpace ℝ (Fin 2) := rb • e β
      rn • e ν = c • base - s • PlanarRot90 base) :
    let τ : ℝ → ℝ :=
      fun t => if t = β then 2 * Real.pi
        else if t < β then β - t
        else β - t + 2 * Real.pi
    (if 0 < s then
        y < 0 ∧ 0 < c * y + s * x
      else if s < 0 then
        y < 0 ∨ 0 < c * y + s * x
      else
        y < 0) ↔ τ α < τ ν := by sorry
