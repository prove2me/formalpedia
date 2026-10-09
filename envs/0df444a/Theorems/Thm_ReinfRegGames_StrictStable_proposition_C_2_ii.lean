-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_proposition_C_2_ii
-- name    : ReinfRegGames.StrictStable.proposition_C_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:44.049035+00:00
-- url     : https://prove2.me/theorems/54fdbfba-1517-4af4-b7d9-d5fd31aa3ebd
-- title:
--   Proposition C.2(ii), p. 34 — D_h(p, x) ≥ 0, D_h(p, x) = 0 iff p = x, and D_h(p, x) ≥ ½K ‖x − p‖² (C.6)
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on $\Delta=\Delta(B)$ and $p\in\Delta$. $h'(x;p-x)=\lim_{t\to0^+}t^{-1}[h(x+t(p-x))-h(x)]$ is the one-sided derivative (C.3) and $D_h(p,x)=h(p)-h(x)-h'(x;p-x)$ is the Bregman divergence (C.4), which may equal $+\infty$ when $h'(x;p-x)=-\infty$. $\Delta_p=\{x\in\Delta: x_\alpha>0\text{ whenever }p_\alpha>0\}$ is the union of the relative interiors of the faces of $\Delta$ that contain $p$ (C.5).
--
--   For every $x\in\Delta$, $D_h(p,x)\ge0$, $D_h(p,x)=0$ if and only if $p=x$, and
--   $$D_h(p,x)\ \ge\ \tfrac12K\|x-p\|_2^2 .\tag{C.6}$$
--
--   The Bregman divergence is thus a (non-symmetric) measure of proximity to $p$, bounded below by the squared distance.
--
--   **Formalization Note** The one-sided derivative is encoded as the predicate "the difference quotient $t^{-1}[h(x+t(p-x))-h(x)]$ tends to $d$ as $t\to0^+$" with $d$ real, and $D_h(p,x)$ as $h(p)-h(x)-d$; no real-valued function with a junk value stands for $+\infty$. The statement is made for every $x\in\Delta$ at which the one-sided derivative is a real number $d$; where $h'(x;p-x)=-\infty$ the page's $D_h(p,x)=+\infty$ and all three claims hold trivially, so this is the faithful form. The norm in the strong convexity inequality (2.5) is the Euclidean one; the page leaves it unspecified, and since $K$ is existential in Definition 2.1 the class of penalty functions does not depend on this choice, but the constant $K$ does.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 33–34, Proposition C.2(ii) and (C.6), with (C.3)–(C.5)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem proposition_C_2_ii {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (x : B → ℝ) (hx : x ∈ stdSimplex ℝ B) (d : ℝ)
    (hd : Filter.Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds d)) :
    0 ≤ h p - h x - d ∧ (h p - h x - d = 0 ↔ p = x) ∧
      1 / 2 * K * ReinfRegGames.Extinction.sqDist x p ≤ h p - h x - d := by sorry

end ReinfRegGames.StrictStable
