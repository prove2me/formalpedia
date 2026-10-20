-- Prove2me | Theorems.Thm_Plasticity_C0Sum_isometryOn_of_extreme_eq
-- name    : Plasticity.C0Sum.isometryOn_of_extreme_eq
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:39.733139+00:00
-- url     : https://prove2.me/theorems/5ebf2ba2-6d07-4ec1-bad5-7a9757af3066
-- title:
--   A nonexpansive bijection of $c_0$-sum balls that agrees with block isometries at extreme target blocks is an isometry
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of real normed spaces over an arbitrary index set, each of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, and let $(E'_k)_{k\in K}$ be any family of real normed spaces; let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$.
--   Let $F\colon X\to Y$ map $B_X$ bijectively onto $B_Y$ and be $1$-Lipschitz on $B_X$.
--   Let $\sigma\colon I\to K$ be a bijection and $L_i\colon E_i\to E'_{\sigma(i)}$ surjective linear isometries such that for every $x\in B_X$ and $i\in I$ we have $\|F(x)_{\sigma(i)}\|\le\|x_i\|$, and $L_i(x_i)=F(x)_{\sigma(i)}$ whenever $F(x)_{\sigma(i)}$ is an extreme point of the closed unit ball of $E'_{\sigma(i)}$.
--   Then $$\|F(x)-F(y)\|=\|x-y\|\qquad(x,y\in B_X).$$
--   No hypothesis on the target blocks is needed beyond the isometries $L_i$.
-- source:
--   This repository: claim CUB101 (claims/cub.md), the normalization in expositions/c0_separated_edge_planes.md §4, with the no-collapse argument and ending of claim CUB100 (expositions/c0_one_general_plane.md §§5–6)

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem isometryOn_of_extreme_eq {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i))
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖)
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E' ⊤) (σ i) ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1) →
        L i ((x : lp E ⊤) i) = (F x : lp E' ⊤) (σ i)) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F x - F y‖ = ‖x - y‖ := by sorry
end Plasticity.C0Sum
