-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_eq_36_centered
-- name    : RandomLeadGBS.Diffusion.eq_36_centered
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T11:54:14.952179+00:00
-- url     : https://prove2.me/theorems/ddb49338-9057-4f8a-ad90-3d64f8a08cf1
-- title:
--   (36), p. 23 (arbitrary centering) — $EY^r(\infty)/\sqrt r-E\hat Y^r(\infty)/\sqrt r\to0$
-- statement:
--   Under the standing assumptions, with an arbitrary centering $x_*(r)$, take stationary distributions of the GBS chain and of the artificial chain for all sufficiently large $r$. Then, for all sufficiently large $r$, the means $\mathbb E Y^r(\infty)$ and $\mathbb E\hat Y^r(\infty)$ are finite, and
--   $$\frac{\mathbb E Y^r(\infty)}{\sqrt r}-\frac{\mathbb E\hat Y^r(\infty)}{\sqrt r}\to0,\qquad r\to\infty. \tag{36}$$
--   The difference is unchanged by subtracting the common centering $x_*(r)$ from both variables. Together with Lemma 5, Lemma 8 and Lemma 9 (all with general centering), this gives Theorem 1.
--
--   **Formalization Note** Finiteness of both means is part of the conclusion. This is (36) with an arbitrary centering; the paper assumes $x_*\equiv0$ without loss of generality (p. 12), but for real $x_*$ the general chain is not a relabeling of the $x_*\equiv0$ chain.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 23, (36) and its proof (37)–(47); general centering per p. 12

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion
open Filter Topology

theorem eq_36_centered (P : Params) (hP : P.Standing)
    (p : ℝ → State → ℝ) (hp : ∀ᶠ r in atTop, IsStationary P r (p r))
    (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r)) :
    (∀ᶠ r in atTop, Summable (fun s : State => p r s * (s.1 : ℝ)) ∧
      Summable (fun j : ℤ => q r j * (j : ℝ))) ∧
    Tendsto (fun r => ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
      ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r)) atTop (𝓝 0) := by sorry

end RandomLeadGBS.Diffusion
