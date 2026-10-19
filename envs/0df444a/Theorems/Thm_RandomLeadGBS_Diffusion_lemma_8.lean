-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_8
-- name    : RandomLeadGBS.Diffusion.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:11.684875+00:00
-- url     : https://prove2.me/theorems/69001468-130f-4cd9-919f-672021589315
-- title:
--   Lemma 8, p. 22 — Ŷ^r(∞) ≤st Y^r(∞) and T̂^r(∞) ≥st T^r(∞)
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, fix $r>0$, a stationary distribution $p$ of the GBS chain $(Y^r,Z^r)$ and a stationary distribution $q$ of the artificial chain $\hat Y^r$. Then
--   $$
--   \hat Y^r(\infty) \le_{st} Y^r(\infty), \tag{29}
--   $$
--   $$
--   \hat T^r(\infty) \ge_{st} T^r(\infty), \tag{30}
--   $$
--   where $X_1\le_{st}X_2$ means $\mathbb P\{X_1>x\}\le\mathbb P\{X_2>x\}$ for every real $x$, and $T^r$, $\hat T^r$ are the truncated targets (5) evaluated at $Y^r$, $\hat Y^r$.
--
--   The artificial chain's up-rate $\beta\lceil T(j)\rceil$ never exceeds the GBS chain's item rate $\beta Z$ at the same level $j$, which is why the artificial inventory level is stochastically smaller, and its truncated target larger.
--
--   **Formalization Note** Each probability $\mathbb P\{\cdot>x\}$ is the series of the stationary masses of the states where the event holds. Centering $x_*\equiv 0$.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 22, Lemma 8, (29)–(30)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem lemma_8 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) (r : ℝ) (hr : 0 < r)
    (p : State → ℝ) (hp : IsStationary P r p) (q : ℤ → ℝ) (hq : IsArtStationary P r q) :
    (∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0)) ∧
    (∀ x : ℝ, ∑' s : State, (if x < truncTarget P r s.1 then p s else 0) ≤
      ∑' j : ℤ, (if x < truncTarget P r j then q j else 0)) := by sorry

end RandomLeadGBS.Diffusion
