-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_proposition_C_3
-- name    : ReinfRegGames.Extinction.proposition_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:13:43.143817+00:00
-- url     : https://prove2.me/theorems/81616f24-b5ec-48fd-a5ad-ce4f47ba1fb5
-- title:
--   Proposition C.3, p. 35 — $F_h(p,y)\ge\frac12K\|Q(y)-p\|^2$
-- statement:
--   Let $h$ be a penalty function on the simplex $\Delta=\Delta(B)$ with strong convexity constant $K>0$ (Definition 2.1, Euclidean norm), let $p\in\Delta$, and let $y\in\mathbb R^B$ be a score vector with $x=Q(y)$, i.e. $x\in\Delta$ maximizes $\langle y|x'\rangle-h(x')$ over $\Delta$. Then the Fenchel coupling $F_h(p,y)=h(p)+h^*(y)-\langle y|p\rangle$ satisfies
--
--   $$
--   F_h(p,y)\ \ge\ \tfrac12K\,\|Q(y)-p\|_2^2 .
--   $$
--
--   In particular $F_h(p,y)\ge0$, the form in which the inequality enters the proof of Theorem 4.1 (as $F_k(p'_k,y_k)\ge0$, before (4.8)). The bound holds at every $y$, including those for which $Q(y)$ lies on the boundary of the simplex outside $\Delta_p$. Moreover, for every sequence of score vectors $y_j$ with $x_j=Q(y_j)$,
--
--   $$
--   F_h(p,y_j)\to0 \iff x_j\to p .
--   $$
--
--   **Formalization Note** This item is the first sentence of Proposition C.3 (the inequality and the "$F_h(p,y)\to0$ if and only if $Q(y)\to p$" clause, read along sequences); (C.11) is the separate item `eq_C_11`. The norm is the Euclidean norm of the definition of penalty function.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 35, Proposition C.3 (first sentence; proof (C.12)–(C.14))

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.Extinction

theorem proposition_C_3 {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (y x : B → ℝ) (hQ : IsChoice h y x) :
    1 / 2 * K * sqDist x p ≤ fenchelCoupling h p y ∧
      ∀ ys xs : ℕ → B → ℝ, (∀ j, IsChoice h (ys j) (xs j)) →
        (Filter.Tendsto (fun j => fenchelCoupling h p (ys j)) Filter.atTop (nhds 0) ↔
          Filter.Tendsto xs Filter.atTop (nhds p)) := by sorry

end ReinfRegGames.Extinction
