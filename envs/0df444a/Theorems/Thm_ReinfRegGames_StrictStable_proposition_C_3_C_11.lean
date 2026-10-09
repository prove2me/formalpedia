-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_proposition_C_3_C_11
-- name    : ReinfRegGames.StrictStable.proposition_C_3_C_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:17.288257+00:00
-- url     : https://prove2.me/theorems/27115e27-3058-4789-999f-0832d5051ebf
-- title:
--   Proposition C.3, (C.11), p. 35 — F_h(p, y) = D_h(p, x) whenever Q(y) = x and x ∈ Δ_p
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on $\Delta=\Delta(B)$, $p\in\Delta$, and let $F_h(p,y)=h(p)+h^*(y)-\langle y|p\rangle$ be the Fenchel coupling. $h'(x;p-x)=\lim_{t\to0^+}t^{-1}[h(x+t(p-x))-h(x)]$ is the one-sided derivative (C.3) and $D_h(p,x)=h(p)-h(x)-h'(x;p-x)$ is the Bregman divergence (C.4), which may equal $+\infty$ when $h'(x;p-x)=-\infty$. $\Delta_p=\{x\in\Delta: x_\alpha>0\text{ whenever }p_\alpha>0\}$ is the union of the relative interiors of the faces of $\Delta$ that contain $p$ (C.5).
--
--   If $x=Q(y)$ and $x\in\Delta_p$, then the one-sided derivative $h'(x;p-x)$ exists and equals $h(p)-h(x)-F_h(p,y)$, i.e.
--   $$F_h(p,y)=D_h(p,x).\tag{C.11}$$
--
--   This identifies the dual sublevel set $U^*_\varepsilon=\{y:F_h(x^*,y)<\varepsilon K_{\min}/2\}$ with the preimage under $Q$ of the primal set $U_\varepsilon$ defined through Bregman divergences, which is the last step of the proof of Theorem 5.2, Part IV.
--
--   **Formalization Note** The one-sided derivative is encoded as the predicate "the difference quotient $t^{-1}[h(x+t(p-x))-h(x)]$ tends to $d$ as $t\to0^+$" with $d$ real, and $D_h(p,x)$ as $h(p)-h(x)-d$; no real-valued function with a junk value stands for $+\infty$. The conclusion asserts both that the one-sided derivative exists and that its value is $h(p)-h(x)-F_h(p,y)$.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 33–35, Proposition C.3, display (C.11), with (C.3)–(C.5), (C.10)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem proposition_C_3_C_11 {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (y x : B → ℝ) (hx : ReinfRegGames.Extinction.IsChoice h y x)
    (hxp : ∀ α, 0 < p α → 0 < x α) :
    Filter.Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (h p - h x - ReinfRegGames.Extinction.fenchelCoupling h p y)) := by sorry

end ReinfRegGames.StrictStable
