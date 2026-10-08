-- Prove2me | Theorems.Thm_UnitCircleCyclicAngleBasicOrder
-- name    : UnitCircleCyclicAngleBasicOrder
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:45.696778+00:00
-- url     : https://prove2.me/theorems/70349726-f86e-4702-a01c-3cf6639736bd
-- title:
--   Unit Circle Cyclic Angle Basic Order
-- statement:
--   Let $p\in\mathbb R^2$, let $S$ be a finite set, and suppose
--   $|S|\ge 3$.  Assume that each
--   $x\in S$ has been assigned an angle $\theta_x\in[0,2\pi)$ such that
--   $$
--     x=p+(\cos\theta_x,\sin\theta_x),
--   $$
--   and that the map $x\mapsto\theta_x$ is injective.  Then the elements of
--   $S$ admit a cyclic successor map $\sigma$ and lifted endpoint angles
--   $\Theta_x$ with the following properties: $\sigma$ is bijective,
--   $\sigma(x)\ne x$, unordered consecutive endpoint pairs determine $x$,
--   $\Theta_x$ is either $\theta_{\sigma(x)}$ or
--   $\theta_{\sigma(x)}+2\pi$,
--   $$
--     \sigma(x)=p+(\cos\Theta_x,\sin\Theta_x),
--   $$
--   and
--   $$
--     \theta_x<\Theta_x<\theta_x+2\pi
--   $$
--   for every $x\in S$.  Moreover the open angular gap from
--   $\theta_x$ to $\Theta_x$ contains no point of $S$: for all
--   $x,y\in S$ and $0<t<1$,
--   $$
--     y\ne p+\bigl(\cos((1-t)\theta_x+t\Theta_x),
--                  \sin((1-t)\theta_x+t\Theta_x)\bigr),
--   $$
--   and distinct open gaps are disjoint: if $x\ne y$ and $0<s,t<1$, then
--   $$
--     p+\bigl(\cos((1-s)\theta_x+s\Theta_x),
--             \sin((1-s)\theta_x+s\Theta_x)\bigr)
--     \ne
--     p+\bigl(\cos((1-t)\theta_y+t\Theta_y),
--             \sin((1-t)\theta_y+t\Theta_y)\bigr).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleCyclicAngleBasicOrder`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleCyclicAngleBasicOrder.lean#L1-L599

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort

open Classical
open scoped Fin.NatCast
noncomputable section

lemma UnitCircleCyclicAngleBasicOrder
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (θ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ)
    (hθ_mem : ∀ x, 0 ≤ θ x ∧ θ x < 2 * Real.pi)
    (hθ_point : ∀ x,
      x.1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (θ x) else Real.sin (θ x)))
    (hθ_inj : Function.Injective θ)
    (hcard : 3 ≤ S.card) :
    ∃ (succ :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          {x : EuclideanSpace ℝ (Fin 2) // x ∈ S})
      (startAngle endAngle :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ),
      Function.Bijective succ ∧
      (∀ x, x.1 ≠ (succ x).1) ∧
      (∀ x y,
        (Sym2.mk x.1 (succ x).1 :
            Sym2 (EuclideanSpace ℝ (Fin 2))) =
          Sym2.mk y.1 (succ y).1 →
        x = y) ∧
      (∀ x, 0 ≤ startAngle x ∧ startAngle x < 2 * Real.pi) ∧
      (∀ x,
        x.1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (startAngle x) else
                Real.sin (startAngle x))) ∧
      (∀ x,
        (succ x).1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (endAngle x) else
                Real.sin (endAngle x))) ∧
      (∀ x, endAngle x = startAngle (succ x) ∨
        endAngle x = startAngle (succ x) + 2 * Real.pi) ∧
      (∀ x, startAngle x < endAngle x) ∧
      (∀ x, endAngle x < startAngle x + 2 * Real.pi) ∧
      (∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (t : ℝ),
        0 < t → t < 1 →
          y.1 ≠
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - t) * startAngle x + t * endAngle x)
                else
                  Real.sin ((1 - t) * startAngle x + t * endAngle x))) ∧
      (∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (s t : ℝ),
        x ≠ y → 0 < s → s < 1 → 0 < t → t < 1 →
          p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - s) * startAngle x + s * endAngle x)
                else
                  Real.sin ((1 - s) * startAngle x + s * endAngle x)) ≠
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - t) * startAngle y + t * endAngle y)
                else
                  Real.sin ((1 - t) * startAngle y + t * endAngle y))) := by sorry
