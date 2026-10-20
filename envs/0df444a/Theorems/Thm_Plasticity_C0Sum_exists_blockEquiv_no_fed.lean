-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_no_fed
-- name    : Plasticity.C0Sum.exists_blockEquiv_no_fed
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:35.023987+00:00
-- url     : https://prove2.me/theorems/51a8ff13-d2ba-4526-8891-3b6925a6cf00
-- title:
--   No fed blocks: under forward support, a nonexpansive bijection between the balls of $c_0$ sums of lines and non-parallelogram planes sends scalar blocks to scalar blocks
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, each block of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points.
--   Let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$, and write $x_i$ for the block of $x$ at $i$.
--   Let $F\colon X\to Y$ map $B_X$ bijectively onto $B_Y$ and be $1$-Lipschitz on $B_X$.
--   Let $\sigma\colon I\to K$ be a map with the following properties.
--
--   - *Forward support:* for every $x\in B_X$ and $n\in K$, if $x_i=0$ for every $i$ with $\sigma(i)=n$, then $F(x)_n=0$.
--   - If $\dim E_i=2$, then $i$ is the only index with image $\sigma(i)$.
--   - If $\dim E'_{\sigma(h)}=1$, then $h$ is the only index with image $\sigma(h)$.
--   - Every fibre of $\sigma$ has at most two elements.
--
--   Then $\dim E'_{\sigma(h)}=1$ for every $h\in I$ with $\dim E_h=1$.
--   Neither surjectivity of $\sigma$ nor $\dim E'_{\sigma(i)}=2$ for planar $i$ is assumed.
-- source:
--   This repository: claim CUB109 (claims/cub.md), Lemmas 3.1–3.2 and Proposition 3.3 in expositions/c0_planes_with_scalars.md §3

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem exists_blockEquiv_no_fed {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ (Module.finrank ℝ (E' k) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E' k) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (σ : ι → κ)
    (hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n : κ,
      (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0)
    (hplane : ∀ i, Module.finrank ℝ (E i) = 2 → ∀ k, σ k = σ i → k = i)
    (hscal : ∀ h h', Module.finrank ℝ (E' (σ h)) = 1 → σ h' = σ h → h' = h)
    (hthree : ∀ a b c, σ a = σ b → σ a = σ c → a = b ∨ a = c ∨ b = c) :
    ∀ h, Module.finrank ℝ (E h) = 1 → Module.finrank ℝ (E' (σ h)) = 1 := by sorry
end Plasticity.C0Sum
