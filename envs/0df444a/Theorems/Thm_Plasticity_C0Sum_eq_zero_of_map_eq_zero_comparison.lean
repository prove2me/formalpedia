-- Prove2me | Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_comparison
-- name    : Plasticity.C0Sum.eq_zero_of_map_eq_zero.comparison
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:27.544373+00:00
-- url     : https://prove2.me/theorems/12c3e16f-01e7-4ec4-b42c-568b2040f8b2
-- title:
--   Comparison at extreme points for a normalized nonexpansive surjection of the ball of a $c_0$ sum
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of real normed spaces over an arbitrary index set such that every nonzero point $b$ of the closed unit ball of each $E_i$ satisfies $\|b-e\|\le1$ for some extreme point $e$ of that ball, and let $X=c_0(I;E_i)$ carry the supremum block norm, with closed unit ball $B$.
--   Let $F\colon X\to X$ be $1$-Lipschitz on $B$ with $B\subseteq F(B)$, and suppose that for every $x\in B$ and $i\in I$ we have $x_i=F(x)_i$ whenever the block $F(x)_i$ is an extreme point of the closed unit ball of $E_i$.
--   Then $$\|F(x)_i-w\|\le\max\{1,\|x_i-w\|\}$$ for every $x\in B$, every $i\in I$ and every extreme point $w$ of the closed unit ball of $E_i$.
--   Neither injectivity of $F$ on $B$ nor $F(B)\subseteq B$ is assumed, and the blocks may be infinite-dimensional.
-- source:
--   This repository: claim CUB100 (claims/cub.md), Lemma 4.5 in expositions/c0_one_general_plane.md §4

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum.eq_zero_of_map_eq_zero
theorem comparison {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hcov : ∀ i, ∀ b : E i, ‖b‖ ≤ 1 → b ≠ 0 →
      ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1), ‖b - e‖ ≤ 1)
    (F : c0Sum E → c0Sum E)
    (hsurj : Set.SurjOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1) →
        (x : lp E ⊤) i = (F x : lp E ⊤) i)
    (x : c0Sum E) (hx : x ∈ Metric.closedBall (0 : c0Sum E) 1) (i : ι)
    (w : E i) (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)) :
    ‖(F x : lp E ⊤) i - w‖ ≤ max 1 ‖(x : lp E ⊤) i - w‖ := by sorry
end Plasticity.C0Sum.eq_zero_of_map_eq_zero
