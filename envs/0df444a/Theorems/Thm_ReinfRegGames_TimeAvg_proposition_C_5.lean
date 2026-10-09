-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_proposition_C_5
-- name    : ReinfRegGames.TimeAvg.proposition_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:27.275908+00:00
-- url     : https://prove2.me/theorems/f6b571f1-ddd8-40b4-a343-1dfedd9c1020
-- title:
--   Proposition C.5, p. 35 — for interior p, a bounded Fenchel coupling F_h(p, y_j) forces bounded score differences
-- statement:
--   Let $B$ be a finite set, $h$ a penalty function on $\Delta(B)$ (Definition 2.1), and $F_h(p, y) = h(p) + h^*(y) - \langle y | p\rangle$ the Fenchel coupling (C.10). Let $p \in \Delta^\circ$ be an interior point: $p$ is a probability vector with $p_\alpha > 0$ for all $\alpha \in B$. Let $(y_j)_{j \in J}$ be a family of score vectors such that $F_h(p, y_j)$ is bounded. Then for all $\alpha, \beta \in B$ the score differences are bounded:
--   $$\sup_{j \in J} |y_{j,\alpha} - y_{j,\beta}| < \infty .$$
--
--   This is a weak converse of the fact that $F_h(p,y)$ controls the distance of $Q(y)$ to $p$: keeping the coupling to an interior point bounded keeps all relative scores bounded, which is exactly the hypothesis of Theorem 6.1.
--
--   **Formalization Note** The page speaks of a sequence $(y_j)$; the statement is given for a family indexed by an arbitrary type $J$, which is equivalent (a family is bounded iff every sequence drawn from it is) and covers both sequences ($J = \mathbb N$) and trajectories ($J = \mathbb R$).
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 35–36, Proposition C.5

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.TimeAvg

theorem proposition_C_5 {B : Type*} [Fintype B] [DecidableEq B]
    (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : AGT.IsLottery p) (hint : ∀ α, 0 < p α)
    {J : Type*} (y : J → B → ℝ) (hF : ∃ M : ℝ, ∀ j, |ReinfRegGames.Extinction.fenchelCoupling h p (y j)| ≤ M) :
    ∀ α β : B, ∃ M' : ℝ, ∀ j, |y j α - y j β| ≤ M' := by sorry

end ReinfRegGames.TimeAvg
