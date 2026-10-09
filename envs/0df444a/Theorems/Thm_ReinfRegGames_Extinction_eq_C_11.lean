-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_eq_C_11
-- name    : ReinfRegGames.Extinction.eq_C_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:29.00945+00:00
-- url     : https://prove2.me/theorems/31d7a3e1-1da9-47be-9591-87583d9625ec
-- title:
--   (C.11) of Proposition C.3, p. 35 — $F_h(p,y)=D_h(p,x)$ whenever $Q(y)=x\in\Delta_p$
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on the simplex $\Delta$, let $p\in\Delta$, and let $y$ be a score vector with $x=Q(y)$. If $x\in\Delta_p$, then the one-sided derivative $h'(x;p-x)$ exists, is a real number, and
--
--   $$
--   F_h(p,y)=D_h(p,x)=h(p)-h(x)-h'(x;p-x). \qquad\text{(C.11)}
--   $$
--
--   The identity transfers the continuity of the Bregman divergence on $\Delta_p$ (Proposition C.2(iii)) to the Fenchel coupling, which is how Proposition C.4 is proved.
--
--   **Formalization Note** The statement says that the one-sided derivative of $h$ at $x$ in the direction $p-x$ equals $h(p)-h(x)-F_h(p,y)$, which is (C.11) rearranged and includes the existence of the derivative.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 35, Proposition C.3, (C.11)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Bregman

namespace ReinfRegGames.Extinction

theorem eq_C_11 {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (y x : B → ℝ) (hQ : IsChoice h y x)
    (hx : x ∈ deltaP p) :
    HasOneSidedDeriv h x (p - x) (h p - h x - fenchelCoupling h p y) := by sorry

end ReinfRegGames.Extinction
