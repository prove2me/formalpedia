-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_5
-- name    : RandomLeadGBS.Diffusion.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:27.784701+00:00
-- url     : https://prove2.me/theorems/44b0f319-9826-4c17-bda4-d3d220d9b8e3
-- title:
--   Lemma 5, p. 17 — the artificial chain's stationary Ŷ^r(∞)/√r ⇒ N(0,(βγ)^−1), with E[·]^± → (2πβγ)^−1/2
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, consider the artificial birth–death chain $\hat Y^r$ (down rate $r$, up rate $\beta\lceil\hat T^r(j)\rceil$). Then:
--
--   1. for every $r>0$ the artificial chain has a stationary distribution;
--   2. for every choice of stationary distributions $\hat Y^r(\infty)$, one for each sufficiently large $r$,
--   $$
--   \frac{\hat Y^r(\infty)}{\sqrt r} \Rightarrow \mathcal N\big(0,(\beta\gamma)^{-1}\big), \tag{20}
--   $$
--   $$
--   \mathbb E\Big[\frac{\hat Y^r(\infty)}{\sqrt r}\Big]^+ \to (2\pi\beta\gamma)^{-1/2},\qquad \mathbb E\Big[\frac{\hat Y^r(\infty)}{\sqrt r}\Big]^- \to (2\pi\beta\gamma)^{-1/2}. \tag{21}
--   $$
--   Here $a^+ = a\vee 0$ and $a^- = (-a)\vee 0$. This is Theorem 1 for the artificial process; the main theorem is then transferred to the GBS chain by stochastic comparison.
--
--   **Formalization Note** Weak convergence is stated by its definition: for every bounded continuous $g:\mathbb R\to\mathbb R$, $\sum_j p_r(j)\,g(j/\sqrt r)$ converges to $\int g\,d\mathcal N(0,(\beta\gamma)^{-1})$ (Mathlib's `gaussianReal`). The limits in (21) are the half-normal means of $\mathcal N(0,(\beta\gamma)^{-1})$. Clause 1 ("its stability is easily verified", p. 17) keeps clause 2 from holding vacuously. The printed "$[\hat Y^r(\infty)]/\sqrt r]^+$" has an unbalanced bracket and is read as $[\hat Y^r(\infty)/\sqrt r]^+$. Centering $x_*\equiv 0$.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 17, Lemma 5, (20)–(21)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion
open Filter Topology

theorem lemma_5 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    (∀ r : ℝ, 0 < r → ∃ p : ℤ → ℝ, IsArtStationary P r p) ∧
    ∀ p : ℝ → ℤ → ℝ, (∀ᶠ r in atTop, IsArtStationary P r (p r)) →
      (∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun r => ∑' j : ℤ, p r j * g ((j : ℝ) / Real.sqrt r)) atTop
          (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max ((j : ℝ) / Real.sqrt r) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max (-((j : ℝ) / Real.sqrt r)) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) := by sorry

end RandomLeadGBS.Diffusion
