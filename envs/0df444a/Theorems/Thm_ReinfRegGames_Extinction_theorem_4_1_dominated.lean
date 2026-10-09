-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_theorem_4_1_dominated
-- name    : ReinfRegGames.Extinction.theorem_4_1_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:41.45572+00:00
-- url     : https://prove2.me/theorems/662576d0-ff09-425b-86c9-d40d45f9dc9d
-- title:
--   Theorem 4.1, p. 16 (base case, p. 18) — along every orbit of (RL), every strictly dominated strategy becomes extinct
-- statement:
--   Consider a finite game in normal form, a penalty function $h_\ell$ (Definition 2.1) for every player $\ell$, and an orbit $x(t)=Q(y(t))$, $t\ge0$, of the reinforcement learning dynamics (RL). Let $k$ be a player and $p_k,p'_k\in\mathcal X_k$ mixed strategies such that $p_k$ is dominated by $p'_k$:
--
--   $$
--   u_k(p_k;z_{-k})<u_k(p'_k;z_{-k})\qquad\text{for every mixed profile } z\in\mathcal X. \qquad (4.1)
--   $$
--
--   Then $p_k$ becomes extinct along $x(t)$:
--
--   $$
--   \min\{x_{k\alpha}(t):\ \alpha\in\operatorname{supp}(p_k)\}\ \longrightarrow\ 0\qquad (t\to\infty).
--   $$
--
--   This is the case of Theorem 4.1 for strategies that are dominated in the original game, the base case $r=1$ of the paper's induction. No steepness of the penalty functions is assumed.
--
--   **Formalization Note** Extinction is written without a minimum: for every $\varepsilon>0$ there is $T$ such that for every $t\ge T$ some $\alpha$ with $p_{k\alpha}>0$ has $x_{k\alpha}(t)<\varepsilon$; this is the limit, not a $\liminf$. Every player has a penalty function because the orbit uses every player's choice map.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 16, Theorem 4.1 (dominated case); proof p. 18

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.Extinction

theorem theorem_4_1_dominated {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : IsRLOrbit u h y x)
    (k : ι) (p p' : A k → ℝ) (hp : AGT.IsLottery p) (hp' : AGT.IsLottery p')
    (hdom : ∀ z : ∀ ℓ, A ℓ → ℝ, AGT.IsMixedProfile z →
      AGT.expectedPayoff u (Function.update z k p) k <
        AGT.expectedPayoff u (Function.update z k p') k) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T, ∃ α, 0 < p α ∧ x t k α < ε := by sorry

end ReinfRegGames.Extinction
