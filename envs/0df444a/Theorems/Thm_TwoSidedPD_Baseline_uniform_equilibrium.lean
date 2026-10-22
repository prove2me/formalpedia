-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_uniform_equilibrium
-- name    : TwoSidedPD.Baseline.uniform_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:08.170988+00:00
-- url     : https://prove2.me/theorems/f49424fe-c789-444b-a427-fc4c9f47d8c8
-- title:
--   Display (12), p. 3345 — the uniform-pricing optimum: N_S^U, N_B^U, p^U, f^U, Π^U = 2v²/(8 − (2b+θH+θL)²), and N_j^U (fn. 14)
-- statement:
--   Consider the baseline two-sided platform with stand-alone value $v$, cross-side benefit $b$ and seller types $\theta_H>\theta_L>0$, with $b>0$ and Assumption 1. Write $U=8-(2b+\theta_H+\theta_L)^2$.
--
--   Under uniform pricing the platform's problem $\max_{(N_B,N_S)\in\mathbb R^2}\Pi^U(N_B,N_S)$ has a solution, and every solution satisfies
--   $$N^U_S=\frac{2v(2b+\theta_H+\theta_L)}{U},\quad N^U_B=\frac{4v}{U},\quad p^U=\frac{v\big(4-(\theta_H+\theta_L)(2b+\theta_H+\theta_L)\big)}{U},\quad f^U=\frac{v(\theta_H+\theta_L-2b)}{U},\quad \Pi^U=\frac{2v^2}{U},$$
--   where $p^U=P^U(N^U_B,N^U_S)$ and $f^U=F^U(N^U_B,N^U_S)$. Moreover (footnote 14), the participation of type-$j$ sellers is
--   $$N^U_j=\frac{v(2b+3\theta_j-\theta_{-j})}{U},\qquad j\in\{L,H\}.$$
--
--   These closed forms are the uniform-pricing side of every welfare comparison in Proposition 2.
--
--   **Formalization Note.** The optimum is a global maximizer of $\Pi^U$ over $\mathbb R^2$; existence is part of the statement. $N^U_j$ is the type-$j$ demand $\theta_jN_B-f^U$ at the common fee.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3345, §4.2.1, display (12); p. 3355, footnote 14

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem uniform_equilibrium (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    (∃ x : ℝ × ℝ, IsUniformOpt v b θH θL x) ∧
    ∀ x : ℝ × ℝ, IsUniformOpt v b θH θL x →
      x.2 = 2 * v * (2 * b + θH + θL) / Uden b θH θL ∧
      x.1 = 4 * v / Uden b θH θL ∧
      PU v b x.1 x.2 = v * (4 - (θH + θL) * (2 * b + θH + θL)) / Uden b θH θL ∧
      FU θH θL x.1 x.2 = v * (θH + θL - 2 * b) / Uden b θH θL ∧
      profitU v b θH θL x = 2 * v ^ 2 / Uden b θH θL ∧
      sellerU θH θH θL x = v * (2 * b + 3 * θH - θL) / Uden b θH θL ∧
      sellerU θL θH θL x = v * (2 * b + 3 * θL - θH) / Uden b θH θL := by sorry

end TwoSidedPD.Baseline
