-- Prove2me | Theorems.Thm_Plasticity_C0Sum_isometryOn_of_reduced
-- name    : Plasticity.C0Sum.isometryOn_of_reduced
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:36.610635+00:00
-- url     : https://prove2.me/theorems/4fe27bac-7d3d-4cbb-a20c-606cd43959e2
-- title:
--   Nonexpansive bijections between the balls of $c_0$ sums of lines and non-parallelogram planes are isometries
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, each block of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, and let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$.
--   If $F\colon X\to Y$ maps $B_X$ bijectively onto $B_Y$ and is $1$-Lipschitz on $B_X$, then $$\|F(x)-F(y)\|=\|x-y\|\qquad(x,y\in B_X).$$
-- source:
--   This repository: claim CUB109 (claims/cub.md), the core theorem for two sums of scalar blocks and non-parallelogram planes, proof in expositions/c0_planes_with_scalars.md §§2–4 with inputs CUB100, CUB101, CUB103, CUB106 and CUB108

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem isometryOn_of_reduced {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ (Module.finrank ℝ (E' k) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E' k) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1)) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F x - F y‖ = ‖x - y‖ := by sorry
end Plasticity.C0Sum
