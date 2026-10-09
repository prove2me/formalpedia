-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_eq_4_8
-- name    : ReinfRegGames.Extinction.eq_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:48.869849+00:00
-- url     : https://prove2.me/theorems/274bc248-aa91-4950-9984-5d75626eaaaa
-- title:
--   (4.6)–(4.8), proof of Theorem 4.1, p. 18 — the Fenchel coupling to a dominated strategy grows at least linearly
-- statement:
--   Consider a finite game, a penalty function $h_\ell$ for every player $\ell$, and an orbit $x(t)=Q(y(t))$ of the reinforcement learning dynamics (RL). Fix a player $k$ and two mixed strategies $p_k,p'_k\in\mathcal X_k$, and let $\delta$ be a real number such that
--
--   $$
--   u_k(p'_k;z_{-k})-u_k(p_k;z_{-k})\ \ge\ \delta\qquad\text{for every mixed profile } z\in\mathcal X .
--   $$
--
--   Let $V_k(y_k)=h_k(p_k)-h_k(p'_k)-\langle y_k|p_k-p'_k\rangle$ be the cross-coupling (4.6). Then for every $t\ge0$,
--
--   $$
--   F_k(p_k,y_k(t))\ \ge\ V_k(y_k(0))+\delta\,t .
--   $$
--
--   With $\delta=\delta_k=\min_{x\in\mathcal X}\{u_k(p'_k;x_{-k})-u_k(p_k;x_{-k})\}$ this is (4.8). When $p_k$ is strictly dominated by $p'_k$, $\delta_k>0$ and the Fenchel coupling between $p_k$ and the score of player $k$ diverges to $+\infty$, which by Proposition C.4 drives play away from $p_k$.
--
--   **Formalization Note** The minimum $\delta_k$ is the largest admissible $\delta$, so stating the bound for every admissible $\delta$ is equivalent to stating it for $\delta_k$, without a real infimum. Here $u_k(p;z_{-k})$ is the expected payoff of player $k$ when $z_k$ is replaced by $p$. The orbit is an orbit of (RL) in the differential form of the `Model` definition.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 18, proof of Theorem 4.1, (4.6)–(4.8)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.Extinction

theorem eq_4_8 {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : IsRLOrbit u h y x)
    (k : ι) (p p' : A k → ℝ) (hp : AGT.IsLottery p) (hp' : AGT.IsLottery p') (δ : ℝ)
    (hδ : ∀ z : ∀ ℓ, A ℓ → ℝ, AGT.IsMixedProfile z →
      δ ≤ AGT.expectedPayoff u (Function.update z k p') k -
        AGT.expectedPayoff u (Function.update z k p) k) :
    ∀ t : ℝ, 0 ≤ t →
      (h k p - h k p' - y 0 k ⬝ᵥ (p - p')) + δ * t ≤ fenchelCoupling (h k) p (y t k) := by sorry

end ReinfRegGames.Extinction
