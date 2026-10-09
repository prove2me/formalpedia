-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_proposition_6_2
-- name    : ReinfRegGames.TimeAvg.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:34.949697+00:00
-- url     : https://prove2.me/theorems/8d55c0d1-a34f-487f-922f-2a8907b7b582
-- title:
--   Proposition 6.2, p. 26 — in 2-player zero-sum games with an interior equilibrium, time-averaged (RL) play converges to the Nash set
-- statement:
--   Let $\mathcal G$ be a 2-player zero-sum game, $u_1 = -u_2$, with finite strategy sets $\mathcal A_1, \mathcal A_2$, and suppose $\mathcal G$ has an interior Nash equilibrium $x^*$ (every pure strategy has positive probability under $x^*$). Let each player use a penalty function $h_k$ on $\Delta(\mathcal A_k)$ (Definition 2.1), and let $(y(t), x(t))$ be any orbit of the reinforcement learning dynamics (RL),
--   $$\dot y_k = v_k(x), \qquad x_k = Q_k(y_k) = \arg\max_{x_k' \in \Delta(\mathcal A_k)} \{\langle y_k | x_k'\rangle - h_k(x_k')\}.$$
--   Then the time average $\bar x(t) = t^{-1}\int_0^t x(s)\,ds$ converges to the set $\mathrm{NE}(\mathcal G)$ of mixed Nash equilibria of $\mathcal G$:
--   $$\operatorname{dist}\big(\bar x(t), \mathrm{NE}(\mathcal G)\big) \to 0 \qquad (t \to \infty).$$
--
--   The trajectory $x(t)$ itself need not converge (in Matching Pennies it cycles, possibly hitting the boundary of the strategy space infinitely often), but its time average does. The result holds for every penalty function, steep or not, and so covers both the replicator dynamics and the projection dynamics.
--
--   **Formalization Note** Players are indexed by `Fin 2`, and $u_1 = -u_2$ is $u_0(s) + u_1(s) = 0$ for every pure profile $s$. Interiority is $x^*_{k\alpha} > 0$ for all $k, \alpha$. Distances are those of Lean's sup metric on profiles; the Nash set contains $x^*$, so the distance is to a nonempty set. (RL) is used in its differential form, equivalent to the integral form on p. 7. No steepness is assumed on the penalty functions, and strong convexity is stated for the Euclidean norm.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 26, Proposition 6.2

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_TimeAvg_TimeAverage

namespace ReinfRegGames.TimeAvg

theorem proposition_6_2 {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ) (hzs : ∀ s, u 0 s + u 1 s = 0)
    (xstar : ∀ k, A k → ℝ) (hNash : AGT.IsMixedNash u xstar) (hint : ∀ k α, 0 < xstar k α)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x) :
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := by sorry

end ReinfRegGames.TimeAvg
