-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_proposition_C_2_i
-- name    : ReinfRegGames.Extinction.proposition_C_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:18.475028+00:00
-- url     : https://prove2.me/theorems/c57b9e3d-cc10-466e-9d67-1d27572161b4
-- title:
--   Proposition C.2(i), p. 34 — $D_h(p,x)<+\infty$ for $x\in\Delta_p$
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on the simplex $\Delta$ and $p\in\Delta$. If $x\in\Delta_p$, that is, $x\in\Delta$ and $x_\alpha>0$ whenever $p_\alpha>0$, then the one-sided derivative
--
--   $$
--   h'(x;p-x)=\lim_{t\to0^+}\frac{h(x+t(p-x))-h(x)}{t}
--   $$
--
--   exists and is a real number. Equivalently, the Bregman divergence $D_h(p,x)=h(p)-h(x)-h'(x;p-x)$ of (C.4) is finite: $D_h(p,x)<+\infty$.
--
--   This finiteness is what allows Proposition C.4 to conclude that a diverging Fenchel coupling keeps play away from $\Delta_p$.
--
--   **Formalization Note** Finiteness is stated as the existence of a real limit in the predicate `HasOneSidedDeriv`.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 34, Proposition C.2(i)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Bregman

namespace ReinfRegGames.Extinction

theorem proposition_C_2_i {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (x : B → ℝ) (hx : x ∈ deltaP p) :
    ∃ d : ℝ, HasOneSidedDeriv h x (p - x) d := by sorry

end ReinfRegGames.Extinction
