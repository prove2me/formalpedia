-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_proposition_C_2_iii
-- name    : ReinfRegGames.StrictStable.proposition_C_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:24.83749+00:00
-- url     : https://prove2.me/theorems/3fd134ed-ff48-48a9-96dc-8a8b32283e4c
-- title:
--   Proposition C.2(iii), p. 34 — D_h(p, x_j) → D_h(p, x) whenever x_j → x in Δ_p
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on $\Delta=\Delta(B)$ and $p\in\Delta$. $h'(x;p-x)=\lim_{t\to0^+}t^{-1}[h(x+t(p-x))-h(x)]$ is the one-sided derivative (C.3) and $D_h(p,x)=h(p)-h(x)-h'(x;p-x)$ is the Bregman divergence (C.4), which may equal $+\infty$ when $h'(x;p-x)=-\infty$. $\Delta_p=\{x\in\Delta: x_\alpha>0\text{ whenever }p_\alpha>0\}$ is the union of the relative interiors of the faces of $\Delta$ that contain $p$ (C.5).
--
--   If $x_j\to x$ with all $x_j$ and $x$ in $\Delta_p$, then
--   $$D_h(p,x_j)\ \longrightarrow\ D_h(p,x)\qquad(j\to\infty).$$
--
--   Continuity of $D_h(p,\cdot)$ on $\Delta_p$ is what makes the set $U_\varepsilon=\{x:\sum_kD_{h_k}(x^*_k,x_k)<\varepsilon K_{\min}/2\}$ in the proof of Theorem 5.2 a neighbourhood of the vertex $x^*$ (the case $x=p$).
--
--   **Formalization Note** The one-sided derivative is encoded as the predicate "the difference quotient $t^{-1}[h(x+t(p-x))-h(x)]$ tends to $d$ as $t\to0^+$" with $d$ real, and $D_h(p,x)$ as $h(p)-h(x)-d$; no real-valued function with a junk value stands for $+\infty$. By part (i) the derivatives $d_j$ at $x_j$ and $d$ at $x$ exist; the statement takes them as data with the defining limit as hypothesis and concludes $h(p)-h(x_j)-d_j\to h(p)-h(x)-d$.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 33–34, Proposition C.2(iii), with (C.3)–(C.5)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem proposition_C_2_iii {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B)
    (xs : ℕ → B → ℝ) (ds : ℕ → ℝ) (x : B → ℝ) (d : ℝ)
    (hxs : ∀ j, xs j ∈ stdSimplex ℝ B ∧ ∀ α, 0 < p α → 0 < xs j α)
    (hx : x ∈ stdSimplex ℝ B ∧ ∀ α, 0 < p α → 0 < x α)
    (hds : ∀ j, Filter.Tendsto (fun t : ℝ => (h (xs j + t • (p - xs j)) - h (xs j)) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ds j)))
    (hd : Filter.Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds d))
    (hlim : Filter.Tendsto xs Filter.atTop (nhds x)) :
    Filter.Tendsto (fun j => h p - h (xs j) - ds j) Filter.atTop (nhds (h p - h x - d)) := by sorry

end ReinfRegGames.StrictStable
