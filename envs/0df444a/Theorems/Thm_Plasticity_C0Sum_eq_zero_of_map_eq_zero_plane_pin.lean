-- Prove2me | Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_pin
-- name    : Plasticity.C0Sum.eq_zero_of_map_eq_zero.plane_pin
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:24.569061+00:00
-- url     : https://prove2.me/theorems/34c90203-2153-4b9c-8b66-9bbcbfda882c
-- title:
--   The pin lemma for planes: near the comparison point, a block at distance one from the first lift is pulled within $1-t$ of it
-- statement:
--   Let $V$ be a real normed space of dimension $2$ with closed unit ball $D$, and let $q,x\in V$ satisfy $\|q\|\le1$, $\|q-2x\|\le1$ and $\|q-x\|=1$.
--   Then there are an extreme point $w$ of $D$ with $\|w-2x\|\le1$ and $t_0>0$ such that for every $0<t<t_0$, writing $b_t=(1-2t)x+tw$, there is $\rho>0$ with the following property: all $\beta,y\in V$ with $$\|\beta\|\le\|b_t\|,\quad \|\beta-w\|\le1-t,\quad \|y-b_t\|<\rho,\quad \|\beta-\omega\|\le\max\{1,\|y-\omega\|\}\ \text{for every extreme point }\omega\text{ of }D$$ satisfy $\|q-y\|\le1-t$.
--   No condition on the number of extreme points of $D$ is needed.
-- source:
--   This repository: claim CUB100 (claims/cub.md), the pins of types (a)–(c) in the proof of Proposition 5.1, expositions/c0_one_general_plane.md §5

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.C0Sum.eq_zero_of_map_eq_zero
theorem plane_pin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (q x : V)
    (hq : ‖q‖ ≤ 1) (hq2 : ‖q - (2 : ℝ) • x‖ ≤ 1) (hq1 : ‖q - x‖ = 1) :
    ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖w - (2 : ℝ) • x‖ ≤ 1 ∧
      ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : V,
        ‖β‖ ≤ ‖(1 - 2 * t) • x + t • w‖ → ‖β - w‖ ≤ 1 - t →
        ‖y - ((1 - 2 * t) • x + t • w)‖ < ρ →
        (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
          ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
        ‖q - y‖ ≤ 1 - t := by sorry
end Plasticity.C0Sum.eq_zero_of_map_eq_zero
