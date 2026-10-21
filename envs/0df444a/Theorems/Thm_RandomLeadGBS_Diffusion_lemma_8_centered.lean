-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_8_centered
-- name    : RandomLeadGBS.Diffusion.lemma_8_centered
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T11:47:45.328994+00:00
-- url     : https://prove2.me/theorems/96347645-dd0c-4f25-8032-75ed363ecf21
-- title:
--   Lemma 8, p. 22 (arbitrary centering) — $\hat Y^r(\infty)\le_{st}Y^r(\infty)$ and $\hat T^r(\infty)\ge_{st}T^r(\infty)$
-- statement:
--   Under the standing assumptions, with an arbitrary centering $x_*(r)$, fix $r>0$, a stationary distribution $p$ of the GBS chain $(Y^r,Z^r)$ and a stationary distribution $q$ of the artificial chain $\hat Y^r$. Then
--   $$\hat Y^r(\infty)\le_{st}Y^r(\infty),\qquad \hat T^r(\infty)\ge_{st}T^r(\infty),$$
--   that is, $\mathbb P\{\hat Y>x\}\le\mathbb P\{Y>x\}$ and $\mathbb P\{T(Y)>x\}\le\mathbb P\{T(\hat Y)>x\}$ for every real $x$, where $T$ is the truncated target (5).
--
--   **Formalization Note** Each probability is the series of the stationary masses of the states where the event holds.
--
--   **Centering.** This is the statement with an arbitrary centering $x_*(r)$, as used in Theorem 1. On p. 12 the paper assumes $x_*\equiv0$ without loss of generality ("If not, we can consider $Y^r-x_*(r)$ instead of $Y^r$, and exactly same proof applies"). Because $x_*$ is real rather than an integer, the chain with general $x_*$ is not a relabeling of the $x_*\equiv0$ chain, so the general version is stated separately; the $x_*\equiv0$ milestone is its special case.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 22, Lemma 8, (29)–(30); general centering per p. 12

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem lemma_8_centered (P : Params) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (p : State → ℝ) (hp : IsStationary P r p) (q : ℤ → ℝ) (hq : IsArtStationary P r q) :
    (∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0)) ∧
    (∀ x : ℝ, ∑' s : State, (if x < truncTarget P r s.1 then p s else 0) ≤
      ∑' j : ℤ, (if x < truncTarget P r j then q j else 0)) := by sorry

end RandomLeadGBS.Diffusion
