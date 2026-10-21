-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_4
-- name    : RandomLeadGBS.Diffusion.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:11.877773+00:00
-- url     : https://prove2.me/theorems/995fba99-d4ad-42f1-858c-824742672128
-- title:
--   Lemma 4, p. 15 — the steady-state gaps satisfy E D^r(∞) ≤ E D̃^r(∞) ≤ C for all large r
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, consider the gaps $D^r = Z^r - \lceil T^r\rceil$ and $\tilde D^r = Z^r - \lceil T^r\wedge X^r\rceil$ of the GBS chain. There are a constant $C>0$ and $r_0$ such that for every $r\ge r_0$ and every stationary distribution of the GBS chain the expectations of $D^r(\infty)$ and $\tilde D^r(\infty)$ exist and
--   $$
--   \mathbb E D^r(\infty) \le \mathbb E\tilde D^r(\infty) \le C .
--   $$
--   The steady-state gap between the in-transit inventory and its truncated target therefore stays bounded as $r\to\infty$, so it vanishes after $1/\sqrt r$ scaling.
--
--   **Formalization Note** The page's "$\sup_r \mathbb E\tilde D^r(\infty)<\infty$", for the sequence $r\to\infty$, is stated as a bound uniform over $r\ge r_0$, matching the lemma's own "for all sufficiently large $r$". Both expectations are series whose summability is asserted. The centering is $x_*\equiv 0$ (p. 12).
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 15, Lemma 4

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem lemma_4 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ p : State → ℝ, IsStationary P r p →
      Summable (fun s => p s * gapD P r s) ∧ Summable (fun s => p s * gapDt P r s) ∧
      ∑' s, p s * gapD P r s ≤ ∑' s, p s * gapDt P r s ∧
      ∑' s, p s * gapDt P r s ≤ C := by sorry

end RandomLeadGBS.Diffusion
