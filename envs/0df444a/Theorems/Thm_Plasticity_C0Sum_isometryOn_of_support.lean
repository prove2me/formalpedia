-- Prove2me | Theorems.Thm_Plasticity_C0Sum_isometryOn_of_support
-- name    : Plasticity.C0Sum.isometryOn_of_support
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:37.178983+00:00
-- url     : https://prove2.me/theorems/0e8902c8-5665-4c02-88de-f55e32f0c7e6
-- title:
--   A support-preserving nonexpansive bijection of the ball of a $c_0$ sum of finite-dimensional spaces is an isometry
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of finite-dimensional real normed spaces over an arbitrary index set, and let $X=c_0(I;E_i)$ carry the supremum block norm, with closed unit ball $B$.
--   Let $F\colon X\to X$ map $B$ bijectively onto $B$, be $1$-Lipschitz on $B$, and preserve supports: $F(x)_i=0$ if and only if $x_i=0$, for every $x\in B$ and $i\in I$.
--   Then $$\|F(x)-F(y)\|=\|x-y\|\qquad(x,y\in B).$$
-- source:
--   This repository: claim CUB100 (claims/cub.md), the ending in expositions/c0_one_general_plane.md §6 before Mankiewicz's theorem, by the Freudenthal–Hurewicz theorem on finitely supported slices (card Plasticity.Ext.FreudenthalHurewicz)

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem isometryOn_of_support {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (F : c0Sum E → c0Sum E)
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i = 0 ↔ (x : lp E ⊤) i = 0) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F x - F y‖ = ‖x - y‖ := by sorry
end Plasticity.C0Sum
