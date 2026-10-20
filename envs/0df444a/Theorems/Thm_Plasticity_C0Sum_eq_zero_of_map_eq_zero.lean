-- Prove2me | Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero
-- name    : Plasticity.C0Sum.eq_zero_of_map_eq_zero
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:32.552203+00:00
-- url     : https://prove2.me/theorems/d07aabf6-4ecb-4c99-be7a-1af4657ba9ff
-- title:
--   No collapse: a normalized nonexpansive bijection of the ball of a $c_0$ sum of lines and non-parallelogram planes keeps every nonzero block nonzero
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of real normed spaces over an arbitrary index set, each of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, and let $X=c_0(I;E_i)$ carry the supremum block norm, with closed unit ball $B$.
--   Let $F\colon X\to X$ map $B$ bijectively onto $B$ and be $1$-Lipschitz on $B$, and suppose that for every $x\in B$ and $i\in I$ we have $\|F(x)_i\|\le\|x_i\|$ (the zero rule), and $x_i=F(x)_i$ whenever $F(x)_i$ is an extreme point of the closed unit ball of $E_i$ (the normalization).
--   Then for every $x\in B$ and $i\in I$, $$F(x)_i=0\implies x_i=0.$$
--   With the zero rule this says that $F(x)$ and $x$ have the same support.
-- source:
--   This repository: claim CUB100 (claims/cub.md), Proposition 5.1 in expositions/c0_one_general_plane.md §5, extended to scalar blocks in claim CUB109 (expositions/c0_planes_with_scalars.md §4)

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem eq_zero_of_map_eq_zero {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (F : c0Sum E → c0Sum E)
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E ⊤) i‖ ≤ ‖(x : lp E ⊤) i‖)
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1) →
        (x : lp E ⊤) i = (F x : lp E ⊤) i)
    (x : c0Sum E) (hx : x ∈ Metric.closedBall (0 : c0Sum E) 1) (i : ι)
    (hFx : (F x : lp E ⊤) i = 0) : (x : lp E ⊤) i = 0 := by sorry
end Plasticity.C0Sum
