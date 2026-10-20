-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_support
-- name    : Plasticity.C0Sum.exists_blockEquiv_support
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:03:19.67369+00:00
-- url     : https://prove2.me/theorems/5fd2d1f4-666c-4134-b6e7-6a73fe2b6e17
-- title:
--   Forward support: nonexpansive bijections between balls of $c_0$ sums of lines and planes have a surjective block map with fibres of at most two blocks
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, each $E_i$ of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, and each $E'_k$ of dimension $1$ or $2$.
--   Let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$, and write $x_i$ for the block of $x$ at $i$.
--   Let $F\colon X\to Y$ map $B_X$ bijectively onto $B_Y$ and be $1$-Lipschitz on $B_X$.
--   Then there is a surjection $\sigma\colon I\to K$ with the following properties.
--
--   - *Forward support:* for every $x\in B_X$ and $n\in K$, if $x_i=0$ for every $i$ with $\sigma(i)=n$, then $F(x)_n=0$.
--   - If $\dim E_i=2$, then $\dim E'_{\sigma(i)}=2$ and $i$ is the only index with image $\sigma(i)$.
--   - If $\dim E'_{\sigma(h)}=1$, then $h$ is the only index with image $\sigma(h)$.
--   - Every fibre of $\sigma$ has at most two elements.
-- source:
--   This repository: claim CUB109 (claims/cub.md), Proposition 2.3 in expositions/c0_planes_with_scalars.md §2, with Lemmas 2.1–2.2 there and claim CUB103 (expositions/c0_planes_front.md §3)

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem exists_blockEquiv_support {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1)) :
    ∃ σ : ι → κ, Function.Surjective σ ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n : κ,
        (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0) ∧
      (∀ i, Module.finrank ℝ (E i) = 2 →
        Module.finrank ℝ (E' (σ i)) = 2 ∧ ∀ k, σ k = σ i → k = i) ∧
      (∀ h h', Module.finrank ℝ (E' (σ h)) = 1 → σ h' = σ h → h' = h) ∧
      (∀ a b c, σ a = σ b → σ a = σ c → a = b ∨ a = c ∨ b = c) := by sorry
end Plasticity.C0Sum
