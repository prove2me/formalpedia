-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_theorem_6_1
-- name    : ReinfRegGames.TimeAvg.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:21.616613+00:00
-- url     : https://prove2.me/theorems/e7825d09-d8ea-43fc-aaca-233061a9d704
-- title:
--   Theorem 6.1, p. 25 — in 2-player games, bounded score differences make the time average of an (RL) orbit converge to the Nash set
-- statement:
--   Let $\mathcal G$ be a 2-player game with finite strategy sets $\mathcal A_1, \mathcal A_2$ and payoffs $u_1, u_2$, let each player use a penalty function $h_k$ (Definition 2.1), and let $(y(t), x(t))$ be an orbit of (RL), $x(t) = Q(y(t))$. Suppose the score differences remain bounded: there is $M$ with
--   $$|y_{k\alpha}(t) - y_{k\beta}(t)| \le M \qquad\text{for all } t \ge 0,\ k = 1, 2,\ \alpha, \beta \in \mathcal A_k .$$
--   Then $\mathcal G$ has a Nash equilibrium, and the time average $\bar x(t) = t^{-1}\int_0^t x(s)\,ds$ converges to the set $\mathrm{NE}(\mathcal G)$ of mixed Nash equilibria:
--   $$\operatorname{dist}\big(\bar x(t), \mathrm{NE}(\mathcal G)\big) \to 0 \qquad (t \to \infty).$$
--
--   This is the reinforcement-learning analogue of the classical result that interior replicator trajectories of 2-player games have time averages converging to the Nash set; bounded score differences replace "staying away from the boundary".
--
--   **Formalization Note** Players are indexed by `Fin 2`; the page states and proves the result only for 2-player games (the proof uses that $v_k$ is linear in the single opponent's strategy). Distances are those of Lean's sup metric on profiles. Because the distance to the empty set is $0$ in Lean, the conclusion includes explicitly that the Nash set is nonempty, which is what the page's proof shows (the ω-limit set of $\bar x(t)$ is nonempty and consists of Nash equilibria); without it the convergence statement would hold vacuously for a game without equilibria.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 25, Theorem 6.1

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_TimeAvg_TimeAverage

namespace ReinfRegGames.TimeAvg

theorem theorem_6_1 {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x)
    (hbdd : ∃ M : ℝ, ∀ t, 0 ≤ t → ∀ k (α β : A k), |y t k α - y t k β| ≤ M) :
    {z : ∀ k, A k → ℝ | AGT.IsMixedNash u z}.Nonempty ∧
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := by sorry

end ReinfRegGames.TimeAvg
