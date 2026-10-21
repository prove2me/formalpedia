-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_4_centered
-- name    : RandomLeadGBS.Diffusion.lemma_4_centered
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T11:47:45.483981+00:00
-- url     : https://prove2.me/theorems/0f524db6-42d8-4ab5-bde2-bce5bd5169f3
-- title:
--   Lemma 4, p. 15 (arbitrary centering) — $\mathbb E D^r(\infty)\le\mathbb E\tilde D^r(\infty)\le C$ for all large $r$
-- statement:
--   Under the standing assumptions, with an arbitrary centering $x_*(r)$, consider the gaps $D^r=Z^r-\lceil T^r\rceil$ and $\tilde D^r=Z^r-\lceil T^r\wedge X^r\rceil$ of the GBS chain. There are a constant $C>0$ and $r_0$ such that for every $r\ge r_0$ and every stationary distribution of the GBS chain, the expectations of $D^r(\infty)$ and $\tilde D^r(\infty)$ exist and
--   $$\mathbb E D^r(\infty)\le\mathbb E\tilde D^r(\infty)\le C.$$
--
--   **Formalization Note** Both expectations are series whose summability is asserted.
--
--   **Centering.** This is the statement with an arbitrary centering $x_*(r)$, as used in Theorem 1. On p. 12 the paper assumes $x_*\equiv0$ without loss of generality ("If not, we can consider $Y^r-x_*(r)$ instead of $Y^r$, and exactly same proof applies"). Because $x_*$ is real rather than an integer, the chain with general $x_*$ is not a relabeling of the $x_*\equiv0$ chain, so the general version is stated separately; the $x_*\equiv0$ milestone is its special case.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 15, Lemma 4; general centering per p. 12

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem lemma_4_centered (P : Params) (hP : P.Standing) :
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ p : State → ℝ, IsStationary P r p →
      Summable (fun s => p s * gapD P r s) ∧ Summable (fun s => p s * gapDt P r s) ∧
      ∑' s, p s * gapD P r s ≤ ∑' s, p s * gapDt P r s ∧
      ∑' s, p s * gapDt P r s ≤ C := by sorry

end RandomLeadGBS.Diffusion
