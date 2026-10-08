-- Prove2me | Theorems.Thm_ReluMIP_Ideal_fm_projection_eq_system7
-- name    : ReluMIP.Ideal.fm_projection_eq_system7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:17.369268+00:00
-- url     : https://prove2.me/theorems/def59097-40a6-4d0d-b61b-0c5705ffa2fb
-- title:
--   App. A.1, (7a)–(7d), p. 14 — Fourier–Motzkin elimination of (5) yields the system (7)
-- statement:
--   Let $f(x)=w\cdot x+b$ and $L,U\in\mathbb R^\eta$ with $L_i<U_i$ for every $i$. Write $\breve L,\breve U$ for the sign-adjusted bounds ($\breve L_i=L_i$, $\breve U_i=U_i$ if $w_i\ge0$, swapped otherwise). The projection onto $(x,y,z)$ of the LP relaxation of the multiple choice formulation (5) equals the set of $(x,y,z)$ satisfying
--
--   $$
--   \begin{aligned}
--   &y\ge w\cdot x+b, &&(7a)\\
--   &y\le\sum_{i\in I}w_ix_i-\sum_{i\in I}w_i\breve L_i(1-z)+\Bigl(b+\sum_{i\notin I}w_i\breve U_i\Bigr)z\quad\forall I\subseteq\operatorname{supp}(w), &&(7b)\\
--   &y\ge\sum_{i\in I}w_ix_i-\sum_{i\in I}w_i\breve U_i(1-z)+\Bigl(b+\sum_{i\notin I}w_i\breve L_i\Bigr)z\quad\forall I\subseteq\operatorname{supp}(w), &&(7c)\\
--   &(x,y,z)\in[L,U]\times\mathbb R_{\ge0}\times[0,1]. &&(7d)
--   \end{aligned}
--   $$
--
--   This is the outcome of eliminating the auxiliary variables $x^0,x^1,y^0,y^1$ of (5) by Fourier–Motzkin elimination.
--
--   **Formalization Note** The page writes (7b) and (7c) with $L,U$ after replacing every negative weight by its absolute value through $\tilde x_i=-x_i$, so its display is the case $w\ge0$; undoing the substitution, as the last paragraph of A.1 does, turns $L,U$ into $\breve L,\breve U$. The Lean states this general-sign form; (7b) is then literally (6b). Strict activity is not assumed (the identity holds without it).
-- source:
--   arXiv:1811.08359v2, App. A.1, display (7a)–(7d), p. 14

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

/-- App. A.1, (7a)–(7d), p. 14 (arXiv:1811.08359v2): eliminating `x⁰, x¹, y⁰, y¹` from the LP
relaxation of (5) by Fourier–Motzkin yields the system (7), written here in general-sign form
(`L̆`, `Ŭ` in place of the page's `L`, `U` for `w > 0`). -/
theorem fm_projection_eq_system7 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) :
    relax5 w b L U = system7 w b L U := by sorry

end ReluMIP.Ideal
