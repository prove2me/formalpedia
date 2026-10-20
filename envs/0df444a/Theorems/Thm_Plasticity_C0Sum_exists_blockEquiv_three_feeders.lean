-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_three_feeders
-- name    : Plasticity.C0Sum.exists_blockEquiv_three_feeders
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:34.449979+00:00
-- url     : https://prove2.me/theorems/19f663dc-2d9a-43de-b35b-f2a6f4051005
-- title:
--   Three scalar blocks cannot feed one planar block of a nonexpansive bijection of $c_0$-sum balls along an open half-plane
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, and let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$.
--   Write $x_i$ for the block of $x$ at $i$, and say that $x$ is supported in block $i$ if $x_l=0$ for every $l\ne i$.
--   Let $F\colon X\to Y$ map $B_X$ bijectively onto $B_Y$ and be $1$-Lipschitz on $B_X$.
--   Let $h_1,h_2,h_3\in I$ be pairwise distinct with $\dim E_{h_k}=1$, and let $e_k\in E_{h_k}$ with $\|e_k\|=1$ for $k=1,2,3$.
--   Let $m\in K$ with $\dim E'_m=2$, and let $\psi$ be a continuous linear functional on $E'_m$.
--   Suppose that for each $k=1,2,3$, every $x\in B_X$ supported in block $h_k$ with $x_{h_k}=\tfrac12e_k$ has $F(x)$ supported in block $m$ and $$\psi\bigl(F(x)_m\bigr)>0.$$
--   Then these hypotheses are contradictory.
-- source:
--   This repository: claim CUB109 (claims/cub.md), Lemma 2.2 in expositions/c0_planes_with_scalars.md §2

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem exists_blockEquiv_three_feeders {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (h : Fin 3 → ι) (hinj : Function.Injective h) (hdim : ∀ k, Module.finrank ℝ (E (h k)) = 1)
    (e : ∀ k, E (h k)) (he : ∀ k, ‖e k‖ = 1)
    (m : κ) (hm : Module.finrank ℝ (E' m) = 2) (ψ : StrongDual ℝ (E' m))
    (hpos : ∀ k, ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (∀ l ≠ h k, (x : lp E ⊤) l = 0) →
      (x : lp E ⊤) (h k) = (1 / 2 : ℝ) • e k →
        (∀ l ≠ m, (F x : lp E' ⊤) l = 0) ∧ 0 < ψ ((F x : lp E' ⊤) m)) : False := by sorry
end Plasticity.C0Sum
