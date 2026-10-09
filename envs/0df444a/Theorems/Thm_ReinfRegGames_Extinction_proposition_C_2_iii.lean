-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_proposition_C_2_iii
-- name    : ReinfRegGames.Extinction.proposition_C_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:19.183008+00:00
-- url     : https://prove2.me/theorems/39611099-8471-4988-8195-ca29b0c88c1a
-- title:
--   Proposition C.2(iii), p. 34 — $D_h(p,x_j)\to D_h(p,x)$ whenever $x_j\to x$ in $\Delta_p$
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on the simplex $\Delta$ and $p\in\Delta$. Let $(x_j)_{j\ge0}$ be a sequence in $\Delta_p$ converging to a point $x\in\Delta_p$. Let $d_j=h'(x_j;p-x_j)$ and $d=h'(x;p-x)$ be the (real) one-sided derivatives of (C.3). Then the Bregman divergences converge:
--
--   $$
--   D_h(p,x_j)=h(p)-h(x_j)-d_j\ \longrightarrow\ h(p)-h(x)-d=D_h(p,x)\qquad (j\to\infty).
--   $$
--
--   Continuity of $D_h(p,\cdot)$ on $\Delta_p$ is the second ingredient, with (C.11), of Proposition C.4.
--
--   **Formalization Note** By Proposition C.2(i) the one-sided derivatives at points of $\Delta_p$ are real numbers; the statement takes them as data satisfying the predicate `HasOneSidedDeriv`.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 34, Proposition C.2(iii)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Bregman

namespace ReinfRegGames.Extinction

open Filter Topology

theorem proposition_C_2_iii {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (xs : ℕ → B → ℝ) (x : B → ℝ)
    (hxs : ∀ j, xs j ∈ deltaP p) (hx : x ∈ deltaP p) (hlim : Tendsto xs atTop (𝓝 x))
    (ds : ℕ → ℝ) (d : ℝ) (hds : ∀ j, HasOneSidedDeriv h (xs j) (p - xs j) (ds j))
    (hd : HasOneSidedDeriv h x (p - x) d) :
    Tendsto (fun j => h p - h (xs j) - ds j) atTop (𝓝 (h p - h x - d)) := by sorry

end ReinfRegGames.Extinction
