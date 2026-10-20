-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_extremeRule
-- name    : Plasticity.C0Sum.exists_extremeRule
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:40.218627+00:00
-- url     : https://prove2.me/theorems/5748cb90-02cc-41e9-a48f-8a668bea15a4
-- title:
--   The extreme rule and the radial inequality for a nonexpansive bijection between the balls of $c_0$ sums of lines and planes
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, each $E_i$ of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, and each $E'_k$ of dimension $1$ or $2$.
--   Let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$, and write $\operatorname{ext}D_V$ for the extreme points of the closed unit ball $D_V$ of a space $V$.
--   Let $F\colon X\to Y$ map $B_X$ bijectively onto $B_Y$ and be $1$-Lipschitz on $B_X$, and let $\sigma\colon I\to K$ be a bijection with $\|F(x)_{\sigma(i)}\|\le\|x_i\|$ for all $x\in B_X$ and $i\in I$.
--   Then for every $i\in I$ there is a map $g\colon E'_{\sigma(i)}\to E_i$ with the following properties.
--
--   - $g$ maps $\operatorname{ext}D_{E'_{\sigma(i)}}$ into $\operatorname{ext}D_{E_i}$, and $g(-w)=-g(w)$ for every $w\in\operatorname{ext}D_{E'_{\sigma(i)}}$.
--   - *Extreme rule:* $x_i=g\bigl(F(x)_{\sigma(i)}\bigr)$ whenever $x\in B_X$ and $F(x)_{\sigma(i)}\in\operatorname{ext}D_{E'_{\sigma(i)}}$.
--   - *Radial inequality:* $\|\alpha w+\beta w'\|\le\|\alpha g(w)+\beta g(w')\|$ for all $w,w'\in\operatorname{ext}D_{E'_{\sigma(i)}}$ and all $\alpha,\beta\in\mathbb R$.
-- source:
--   This repository: claims CUB100 and CUB101 (claims/cub.md), Propositions 4.2–4.4(3) in expositions/c0_one_general_plane.md §4 and the radial inequality (2.2) in expositions/c0_separated_edge_planes.md §2

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem exists_extremeRule {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (σ : ι ≃ κ)
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖) (i : ι) :
    ∃ g : E' (σ i) → E i,
      Set.MapsTo g (Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1))
        (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)) ∧
      (∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), g (-w) = -g w) ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
        (F x : lp E' ⊤) (σ i) ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1) →
          (x : lp E ⊤) i = g ((F x : lp E' ⊤) (σ i))) ∧
      ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1),
        ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), ∀ α β : ℝ,
          ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖ := by sorry
end Plasticity.C0Sum
