-- Prove2me | Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_of_blocks
-- name    : Plasticity.C0Sum.eq_zero_of_map_eq_zero.of_blocks
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:29.956048+00:00
-- url     : https://prove2.me/theorems/749b4834-8607-4d12-93ff-32598c16c2ab
-- title:
--   No collapse in a $c_0$ sum of finite-dimensional blocks with strict coverage, displacement and pins
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of finite-dimensional real normed spaces over an arbitrary index set (zero blocks allowed), and write $D_i$ for the closed unit ball of $E_i$ and $\operatorname{ext}D_i$ for its extreme points.
--   Assume that every block has the following three properties.
--
--   1. *Strict coverage:* every nonzero $b\in D_i$ has $\|b-e\|<1$ for some $e\in\operatorname{ext}D_i$.
--   2. *Displacement:* if $b,z\in E_i$ satisfy $\|b\|\le1$, $\|z\|\le\tfrac12$, and $\|z-w\|\le1$ for every $w\in\operatorname{ext}D_i$ with $\|b-w\|\le1$, then $\|b-2z\|\le1$.
--   3. *Pins:* whenever $q,x\in E_i$ satisfy $\|q\|\le1$, $\|q-2x\|\le1$ and $\|q-x\|=1$, there are $w\in\operatorname{ext}D_i$ with $\|w-2x\|\le1$ and $t_0>0$ such that for every $0<t<t_0$, writing $b_t=(1-2t)x+tw$, there is $\rho>0$ such that all $\beta,y\in E_i$ with $\|\beta\|\le\|b_t\|$, $\|\beta-w\|\le1-t$, $\|y-b_t\|<\rho$, and $\|\beta-\omega\|\le\max\{1,\|y-\omega\|\}$ for every $\omega\in\operatorname{ext}D_i$, satisfy $\|q-y\|\le1-t$.
--
--   Let $X=c_0(I;E_i)$ carry the supremum block norm, with closed unit ball $B$, and let $F\colon X\to X$ map $B$ bijectively onto $B$, be $1$-Lipschitz on $B$, and satisfy, for every $x\in B$ and $i\in I$, $\|F(x)_i\|\le\|x_i\|$, and $x_i=F(x)_i$ whenever $F(x)_i\in\operatorname{ext}D_i$.
--   Then $F(x)_i=0$ implies $x_i=0$ for every $x\in B$ and $i\in I$.
-- source:
--   This repository: claim CUB100 (claims/cub.md), Proposition 5.1 in expositions/c0_one_general_plane.md §5, with the block geometry it uses isolated as three hypotheses

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum.eq_zero_of_map_eq_zero
theorem of_blocks {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (hcov : ∀ i, ∀ b : E i, ‖b‖ ≤ 1 → b ≠ 0 →
      ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖b - e‖ < 1)
    (hdisp : ∀ i, ∀ b z : E i, ‖b‖ ≤ 1 → ‖z‖ ≤ 1 / 2 →
      (∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖b - w‖ ≤ 1 → ‖z - w‖ ≤ 1) →
      ‖b - (2 : ℝ) • z‖ ≤ 1)
    (hpin : ∀ i, ∀ q x : E i, ‖q‖ ≤ 1 → ‖q - (2 : ℝ) • x‖ ≤ 1 → ‖q - x‖ = 1 →
      ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖w - (2 : ℝ) • x‖ ≤ 1 ∧
        ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : E i,
          ‖β‖ ≤ ‖(1 - 2 * t) • x + t • w‖ → ‖β - w‖ ≤ 1 - t →
          ‖y - ((1 - 2 * t) • x + t • w)‖ < ρ →
          (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1),
            ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
          ‖q - y‖ ≤ 1 - t)
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
end Plasticity.C0Sum.eq_zero_of_map_eq_zero
