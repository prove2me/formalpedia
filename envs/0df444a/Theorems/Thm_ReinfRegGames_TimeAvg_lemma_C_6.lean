-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_lemma_C_6
-- name    : ReinfRegGames.TimeAvg.lemma_C_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:19.092681+00:00
-- url     : https://prove2.me/theorems/06b71df0-d8ce-4564-ad91-a12bc4261b96
-- title:
--   Lemma C.6, p. 36 — along (RL), d/dt F_{h_k}(p_k, y_k(t)) = ⟨v_k(x(t)) | x_k(t) − p_k⟩
-- statement:
--   Consider a finite game with players $k$, pure strategy sets $\mathcal A_k$ and payoffs $u_k$, let each player $k$ use a penalty function $h_k$ on $\Delta(\mathcal A_k)$ (Definition 2.1), and let $(y(t), x(t))$ be an orbit of the reinforcement learning dynamics (RL): $x_k(t) = Q_k(y_k(t))$ and $\dot y_k(t) = v_k(x(t))$ for $t \ge 0$, where $v_{k\alpha}(x) = u_k(\alpha; x_{-k})$ is the payoff vector (2.2). Then for every player $k$, every mixed strategy $p_k \in \Delta(\mathcal A_k)$ and every $t \ge 0$,
--   $$\frac{d}{dt} F_{h_k}(p_k, y_k(t)) = \langle v_k(x(t)) \,|\, x_k(t) - p_k \rangle = \sum_{\alpha \in \mathcal A_k} v_{k\alpha}(x(t))\,\big(x_{k\alpha}(t) - p_{k\alpha}\big), \tag{C.16}$$
--   where $F_h(p, y) = h(p) + h^*(y) - \langle y | p\rangle$ is the Fenchel coupling (C.10).
--
--   This identity is the bridge between the dynamics and the game: the rate of change of the Fenchel coupling is the payoff gain of the current strategy over $p_k$, which is how equilibrium properties of $p_k$ translate into monotonicity or conservation of $F_{h_k}$.
--
--   **Formalization Note** The derivative at $t = 0$ is the right derivative (derivative within $[0,\infty)$), as the orbit is only constrained for $t \ge 0$. The statement holds for any finite number of players; it is stated for a general finite player set.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 36, Lemma C.6, (C.16)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.TimeAvg

theorem lemma_C_6 {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x)
    (k : ι) (p : A k → ℝ) (hp : AGT.IsLottery p) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ReinfRegGames.Extinction.fenchelCoupling (h k) p (y s k))
      (∑ α, ReinfRegGames.Extinction.payoffVec u (x t) k α * (x t k α - p α)) (Set.Ici 0) t := by sorry

end ReinfRegGames.TimeAvg
