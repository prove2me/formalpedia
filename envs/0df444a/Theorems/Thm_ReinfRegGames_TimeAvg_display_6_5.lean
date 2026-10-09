-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_display_6_5
-- name    : ReinfRegGames.TimeAvg.display_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:15.526532+00:00
-- url     : https://prove2.me/theorems/3045bb20-6d6b-46e4-ad19-e9d33f432878
-- title:
--   (6.5), proof of Proposition 6.2, p. 26 — in a zero-sum game with an interior equilibrium x*, F_h(x*, y(t)) is constant along (RL)
-- statement:
--   Let $\mathcal G$ be a 2-player game with finite strategy sets $\mathcal A_1, \mathcal A_2$ that is zero-sum, $u_1 = -u_2$, and let $x^* = (x_1^*, x_2^*)$ be an **interior** Nash equilibrium: every pure strategy of every player has positive probability under $x^*$. Let each player use a penalty function $h_k$ (Definition 2.1), and let $(y(t), x(t))$ be an orbit of (RL). Write
--   $$F_h(x^*, y) = \sum_{k=1,2} \big[h_k(x_k^*) + h_k^*(y_k) - \langle y_k | x_k^* \rangle\big]$$
--   for the total Fenchel coupling. Then for every $t \ge 0$,
--   $$\frac{d}{dt} F_h(x^*, y(t)) = \langle v_1(x)|x_1 - x_1^*\rangle + \langle v_2(x)|x_2 - x_2^*\rangle = 0, \tag{6.5}$$
--   and consequently $F_h(x^*, y(t)) = F_h(x^*, y(0))$ for all $t \ge 0$.
--
--   This conservation law is the key step of Proposition 6.2: a constant Fenchel coupling to an interior point keeps the players' score differences bounded (Proposition C.5).
--
--   **Formalization Note** The derivative at $t = 0$ is the right derivative. Players are indexed by `Fin 2` (player 1 is index `0`, player 2 is index `1`), and $u_1 = -u_2$ is $u_0(s) + u_1(s) = 0$ for every pure profile $s$. Both hypotheses, zero-sum and interiority of $x^*$, are used: after $u_2 = -u_1$ the middle expression of (6.5) equals $u_1(x_1, x_2^*) - u_1(x_1^*, x_2)$, which vanishes because at an interior equilibrium each player is indifferent among all of its strategies against the other's equilibrium strategy.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 26, proof of Proposition 6.2, (6.5)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.TimeAvg

theorem display_6_5 {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ) (hzs : ∀ s, u 0 s + u 1 s = 0)
    (xstar : ∀ k, A k → ℝ) (hNash : AGT.IsMixedNash u xstar) (hint : ∀ k α, 0 < xstar k α)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x) :
    (∀ t, 0 ≤ t → HasDerivWithinAt
      (fun s => ∑ k, ReinfRegGames.Extinction.fenchelCoupling (h k) (xstar k) (y s k)) 0 (Set.Ici 0) t) ∧
    ∀ t, 0 ≤ t → ∑ k, ReinfRegGames.Extinction.fenchelCoupling (h k) (xstar k) (y t k) =
      ∑ k, ReinfRegGames.Extinction.fenchelCoupling (h k) (xstar k) (y 0 k) := by sorry

end ReinfRegGames.TimeAvg
