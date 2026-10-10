-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_theorem_4_1
-- name    : ReinfRegGames.Extinction.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:10.136935+00:00
-- url     : https://prove2.me/theorems/649249c8-5ea9-4ad3-96ac-cfa8126a3866
-- title:
--   Theorem 4.1, p. 16 — along every orbit of (RL), every (iteratively) dominated strategy becomes extinct
-- statement:
--   Consider a finite game in normal form with players $k\in\mathcal N$, pure strategy sets $\mathcal A_k$ and payoffs $u_k$; let every player $\ell$ have a penalty function $h_\ell$ on $\mathcal X_\ell=\Delta(\mathcal A_\ell)$ (continuous, smooth on the relative interior of every face, strongly convex, not necessarily steep), and let $x(t)=Q(y(t))$, $t\ge0$, be an orbit of the reinforcement learning dynamics
--
--   $$
--   \dot y_k=v_k(x),\qquad x_k=Q_k(y_k). \qquad\text{(RL)}
--   $$
--
--   Let $\mathcal A^r_k$ be the pure strategies of player $k$ that survive $r$ rounds of iterated elimination of strictly dominated strategies. Fix a round $r\ge0$, a player $k$ and mixed strategies $p_k,p'_k\in\mathcal X_k$ supported on $\mathcal A^r_k$ such that $p'_k$ strictly dominates $p_k$ in the game restricted to the survivors:
--
--   $$
--   u_k(p_k;z_{-k})<u_k(p'_k;z_{-k})\qquad\text{for every mixed profile } z \text{ with } \operatorname{supp}(z_\ell)\subseteq\mathcal A^r_\ell\ \text{for all }\ell .
--   $$
--
--   Then $p_k$ becomes extinct along $x(t)$:
--
--   $$
--   \lim_{t\to\infty}\ \min\{x_{k\alpha}(t):\ \alpha\in\operatorname{supp}(p_k)\}=0 .
--   $$
--
--   For $r=0$ this is the statement for strategies dominated in the original game (4.1); for $r\ge1$ it covers iteratively dominated strategies. Hence only iteratively undominated strategies survive under (RL), for every choice of penalty functions, steep or not, extending the classical elimination results for the replicator dynamics.
--
--   **Formalization Note** Iterated dominance follows the `Dominance` definition: survivors are pure strategies, eliminated at each round by mixed strategies supported on the survivors against profiles supported on the survivors; a mixed strategy is iteratively dominated when it is dominated, in this sense, at some round. (A mixed strategy with weight on an eliminated pure strategy becomes extinct by the statement applied to that pure strategy.) Extinction is written as: for every $\varepsilon>0$ there is $T$ such that for every $t\ge T$ some $\alpha$ with $p_{k\alpha}>0$ has $x_{k\alpha}(t)<\varepsilon$. The orbit is in the differential form of (RL), equivalent to the page's integral form along continuous trajectories.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 16, Theorem 4.1 (proof p. 18)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Dominance

namespace ReinfRegGames.Extinction

theorem theorem_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : IsRLOrbit u h y x)
    (r : ℕ) (k : ι) (p p' : A k → ℝ) (hp : AGT.IsLottery p) (hp' : AGT.IsLottery p')
    (hpS : ∀ α, p α ≠ 0 → α ∈ survivors u r k) (hp'S : ∀ α, p' α ≠ 0 → α ∈ survivors u r k)
    (hdom : ∀ z : ∀ ℓ, A ℓ → ℝ, AGT.IsMixedProfile z →
      (∀ ℓ β, z ℓ β ≠ 0 → β ∈ survivors u r ℓ) →
      AGT.expectedPayoff u (Function.update z k p) k <
        AGT.expectedPayoff u (Function.update z k p') k) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T, ∃ α, 0 < p α ∧ x t k α < ε := by sorry

end ReinfRegGames.Extinction
