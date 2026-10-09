-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_proposition_C_2_i
-- name    : ReinfRegGames.StrictStable.proposition_C_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:52.953006+00:00
-- url     : https://prove2.me/theorems/a3a65cc0-cb75-4dc3-9f1a-b4a9f6d9e561
-- title:
--   Proposition C.2(i), p. 34 — D_h(p, x) < +∞ whenever x ∈ Δ_p
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on $\Delta=\Delta(B)$ and $p\in\Delta$. $h'(x;p-x)=\lim_{t\to0^+}t^{-1}[h(x+t(p-x))-h(x)]$ is the one-sided derivative (C.3) and $D_h(p,x)=h(p)-h(x)-h'(x;p-x)$ is the Bregman divergence (C.4), which may equal $+\infty$ when $h'(x;p-x)=-\infty$. $\Delta_p=\{x\in\Delta: x_\alpha>0\text{ whenever }p_\alpha>0\}$ is the union of the relative interiors of the faces of $\Delta$ that contain $p$ (C.5).
--
--   If $x\in\Delta_p$, then the one-sided derivative $h'(x;p-x)$ exists as a real number; in particular
--   $$D_h(p,x)<+\infty\qquad\text{for all }x\in\Delta_p .$$
--
--   Near a vertex $x^*$, every point of $\Delta$ lies in $\Delta_{x^*}$, so the Bregman divergence $D_h(x^*,\cdot)$ is finite there; the proof of Theorem 5.2 uses this to build the neighbourhood $U_\varepsilon$ of $x^*$.
--
--   **Formalization Note** The one-sided derivative is encoded as the predicate "the difference quotient $t^{-1}[h(x+t(p-x))-h(x)]$ tends to $d$ as $t\to0^+$" with $d$ real, and $D_h(p,x)$ as $h(p)-h(x)-d$; no real-valued function with a junk value stands for $+\infty$.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 33–34, Proposition C.2(i), with (C.3)–(C.5)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem proposition_C_2_i {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (x : B → ℝ) (hx : x ∈ stdSimplex ℝ B)
    (hxp : ∀ α, 0 < p α → 0 < x α) :
    ∃ d : ℝ, Filter.Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by sorry

end ReinfRegGames.StrictStable
