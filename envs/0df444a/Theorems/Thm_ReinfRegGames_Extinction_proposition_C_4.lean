-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_proposition_C_4
-- name    : ReinfRegGames.Extinction.proposition_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:28.395718+00:00
-- url     : https://prove2.me/theorems/2ebae163-ec7a-4b8c-bf6b-70a5f4c82d83
-- title:
--   Proposition C.4, p. 35 — $F_h(p,y_j)\to+\infty$ forces $Q(y_j)$ to have no limit points in $\Delta_p$
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on the simplex $\Delta$ and $p\in\Delta$. Let $(y_j)_{j\ge0}$ be a sequence of score vectors with $F_h(p,y_j)\to+\infty$, and let $x_j=Q(y_j)$. Then
--
--   1. the sequence $(x_j)$ has no limit point (cluster point) in $\Delta_p$;
--   2. in particular,
--   $$
--   \liminf_{j\to\infty}\ \min\{x_{j,\alpha}:\ \alpha\in\operatorname{supp}(p)\}=0 .
--   $$
--
--   Applied along the scores of a player whose Fenchel coupling to $p_k$ diverges, this says that play eventually leaves every neighbourhood of the faces containing $p_k$, i.e. $p_k$ becomes extinct.
--
--   **Formalization Note** Clause 2 is written as: for every $\varepsilon>0$ and every $N$ there is $j\ge N$ and some $\alpha$ with $p_\alpha>0$ and $x_{j,\alpha}<\varepsilon$ (the entries are nonnegative, so this is the $\liminf$ being $0$).
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 35, Proposition C.4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Bregman

namespace ReinfRegGames.Extinction

open Filter Topology

theorem proposition_C_4 {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (ys xs : ℕ → B → ℝ)
    (hQ : ∀ j, IsChoice h (ys j) (xs j))
    (hF : Tendsto (fun j => fenchelCoupling h p (ys j)) atTop atTop) :
    (∀ z ∈ deltaP p, ¬ MapClusterPt z atTop xs) ∧
      ∀ ε > 0, ∀ N : ℕ, ∃ j ≥ N, ∃ α, 0 < p α ∧ xs j α < ε := by sorry

end ReinfRegGames.Extinction
