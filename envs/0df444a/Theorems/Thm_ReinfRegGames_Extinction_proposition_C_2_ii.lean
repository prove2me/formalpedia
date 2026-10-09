-- Prove2me | Theorems.Thm_ReinfRegGames_Extinction_proposition_C_2_ii
-- name    : ReinfRegGames.Extinction.proposition_C_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:26.438268+00:00
-- url     : https://prove2.me/theorems/beca1a30-eb9b-4ee2-b2c5-189a37dd1404
-- title:
--   Proposition C.2(ii), p. 34 — $D_h(p,x)\ge\frac12K\|x-p\|^2$, with $D_h(p,x)=0$ iff $p=x$
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on the simplex $\Delta$ and let $p,x\in\Delta$. Suppose the one-sided derivative $h'(x;p-x)$ is a real number $d$, so that the Bregman divergence $D_h(p,x)=h(p)-h(x)-d$ of (C.4) is finite. Then
--
--   1. $D_h(p,x)\ge0$;
--   2. $D_h(p,x)=0$ if and only if $p=x$;
--   3. $$D_h(p,x)\ \ge\ \tfrac12K\,\|x-p\|_2^2 .\qquad\text{(C.6)}$$
--
--   Together with (C.11), this makes $D_h$ and the Fenchel coupling quantitative measures of the distance between $x$ and $p$.
--
--   **Formalization Note** When $h'(x;p-x)=-\infty$ the page sets $D_h(p,x)=+\infty$, and all three claims hold trivially in the extended reals; the statement therefore quantifies over the points at which the one-sided derivative is a real number. The norm is the Euclidean norm of the definition of penalty function.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 34, Proposition C.2(ii), (C.6)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Bregman

namespace ReinfRegGames.Extinction

theorem proposition_C_2_ii {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (x : B → ℝ) (hx : x ∈ stdSimplex ℝ B) (d : ℝ)
    (hd : HasOneSidedDeriv h x (p - x) d) :
    0 ≤ h p - h x - d ∧ (h p - h x - d = 0 ↔ p = x) ∧
      1 / 2 * K * sqDist x p ≤ h p - h x - d := by sorry

end ReinfRegGames.Extinction
