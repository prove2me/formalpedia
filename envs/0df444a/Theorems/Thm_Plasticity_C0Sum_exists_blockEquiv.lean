-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv
-- name    : Plasticity.C0Sum.exists_blockEquiv
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:30.415456+00:00
-- url     : https://prove2.me/theorems/472d280c-d9b6-4780-9fd7-c199bf0ed3ca
-- title:
--   Block matching: a nonexpansive bijection between the balls of $c_0$ sums of lines and non-parallelogram planes matches blocks of equal dimension and shrinks every block
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, each block of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, and let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$.
--   If $F\colon X\to Y$ maps $B_X$ bijectively onto $B_Y$ and is $1$-Lipschitz on $B_X$, then there is a bijection $\sigma\colon I\to K$ with $\dim E'_{\sigma(i)}=\dim E_i$ for every $i\in I$ and $$\|F(x)_{\sigma(i)}\|\le\|x_i\|\qquad(x\in B_X,\ i\in I).$$
--   So $\sigma$ carries scalar blocks to scalar blocks and planar blocks to planar blocks, and the block $\sigma(i)$ of $F(x)$ vanishes whenever $x_i=0$.
-- source:
--   This repository: claims CUB103 and CUB109 (claims/cub.md), expositions/c0_planes_front.md §3 and expositions/c0_planes_with_scalars.md §§2–3

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem exists_blockEquiv {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ (Module.finrank ℝ (E' k) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E' k) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1)) :
    ∃ σ : ι ≃ κ, (∀ i, Module.finrank ℝ (E' (σ i)) = Module.finrank ℝ (E i)) ∧
      ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
        ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖ := by sorry
end Plasticity.C0Sum
