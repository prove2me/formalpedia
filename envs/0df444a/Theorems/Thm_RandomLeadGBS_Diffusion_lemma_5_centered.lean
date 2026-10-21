-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_5_centered
-- name    : RandomLeadGBS.Diffusion.lemma_5_centered
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T11:47:45.977814+00:00
-- url     : https://prove2.me/theorems/82e1470b-9ee0-4db2-b900-5b2e3d6d75e5
-- title:
--   Lemma 5, p. 17 (arbitrary centering) — $(\hat Y^r(\infty)-x_*)/\sqrt r\Rightarrow N(0,(\beta\gamma)^{-1})$ with $E[\cdot]^\pm\to(2\pi\beta\gamma)^{-1/2}$
-- statement:
--   Under the standing assumptions, with an arbitrary centering $x_*(r)$, consider the artificial birth–death chain $\hat Y^r$ on $\mathbb Z$ (down rate $r$, up rate $\beta\lceil\hat T^r(j)\rceil$). Then:
--
--   1. for every $r>0$ the artificial chain has a stationary distribution;
--   2. for every choice of stationary distributions, one for each sufficiently large $r$,
--   $$\frac{\hat Y^r(\infty)-x_*}{\sqrt r}\Rightarrow\mathcal N\big(0,(\beta\gamma)^{-1}\big),$$
--   $$\mathbb E\Big[\frac{\hat Y^r(\infty)-x_*}{\sqrt r}\Big]^\pm\to(2\pi\beta\gamma)^{-1/2}.$$
--
--   **Formalization Note** Weak convergence is stated by its definition, through bounded continuous test functions and Mathlib's `gaussianReal` with variance $1/(\beta\gamma)$.
--
--   **Centering.** This is the statement with an arbitrary centering $x_*(r)$, as used in Theorem 1. On p. 12 the paper assumes $x_*\equiv0$ without loss of generality ("If not, we can consider $Y^r-x_*(r)$ instead of $Y^r$, and exactly same proof applies"). Because $x_*$ is real rather than an integer, the chain with general $x_*$ is not a relabeling of the $x_*\equiv0$ chain, so the general version is stated separately; the $x_*\equiv0$ milestone is its special case.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 17, Lemma 5, (20)–(21); general centering per p. 12

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion
open Filter Topology

theorem lemma_5_centered (P : Params) (hP : P.Standing) :
    (∀ r : ℝ, 0 < r → ∃ p : ℤ → ℝ, IsArtStationary P r p) ∧
    ∀ p : ℝ → ℤ → ℝ, (∀ᶠ r in atTop, IsArtStationary P r (p r)) →
      (∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun r => ∑' j : ℤ, p r j * g (((j : ℝ) - P.xs r) / Real.sqrt r)) atTop
          (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max (((j : ℝ) - P.xs r) / Real.sqrt r) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) := by sorry

end RandomLeadGBS.Diffusion
