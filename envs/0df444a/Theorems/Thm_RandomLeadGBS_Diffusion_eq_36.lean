-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_eq_36
-- name    : RandomLeadGBS.Diffusion.eq_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:21.573283+00:00
-- url     : https://prove2.me/theorems/8920de30-dd57-419e-b9d5-4d348e6fa390
-- title:
--   (36), p. 23 — EY^r(∞)/√r − EŶ^r(∞)/√r → 0
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, take stationary distributions of the GBS chain and of the artificial chain for all sufficiently large $r$. Then, for all sufficiently large $r$, the means $\mathbb E Y^r(\infty)$ and $\mathbb E\hat Y^r(\infty)$ are finite, and
--   $$
--   \frac{\mathbb E Y^r(\infty)}{\sqrt r} - \frac{\mathbb E\hat Y^r(\infty)}{\sqrt r} \to 0,\qquad r\to\infty. \tag{36}
--   $$
--   By Lemma 5, Lemma 8 and Lemma 9 (applied to $\hat Y^r(\infty)/\sqrt r$ and $Y^r(\infty)/\sqrt r$), this is all that remains to prove Theorem 1.
--
--   **Formalization Note** The finiteness of both means is part of the conclusion: since $\mathbb E\hat Y^r(\infty)/\sqrt r\to 0$, a divergent series evaluated as $0$ would otherwise make (36) easy. Centering $x_*\equiv 0$.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 23, (36); proved in the proof of Theorem 1, pp. 24–25

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion
open Filter Topology

theorem eq_36 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0)
    (p : ℝ → State → ℝ) (hp : ∀ᶠ r in atTop, IsStationary P r (p r))
    (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r)) :
    (∀ᶠ r in atTop, Summable (fun s : State => p r s * (s.1 : ℝ)) ∧
      Summable (fun j : ℤ => q r j * (j : ℝ))) ∧
    Tendsto (fun r => ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
      ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r)) atTop (𝓝 0) := by sorry

end RandomLeadGBS.Diffusion
