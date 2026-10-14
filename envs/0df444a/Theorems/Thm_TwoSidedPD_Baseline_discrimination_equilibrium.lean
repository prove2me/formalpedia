-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_discrimination_equilibrium
-- name    : TwoSidedPD.Baseline.discrimination_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:00.907148+00:00
-- url     : https://prove2.me/theorems/3cd050b9-3ea0-4471-b10b-167ad2e6bed0
-- title:
--   Displays (13)–(15), pp. 3345–3346 — the price-discrimination optimum: N_S^D, N_B^D, N_j^D (fn. 15), p^D, f_j^D, Π^D = v²/D
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1, and write $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$.
--
--   Under price discrimination the platform's problem $\max_{(N_B,N_L,N_H)\in\mathbb R^3}\Pi^D(N_B,N_L,N_H)$ has a solution, and every solution satisfies
--   $$N^D_S=N^D_L+N^D_H=\frac{v(2b+\theta_L+\theta_H)}{D},\qquad N^D_B=\frac{2v}{D},\qquad N^D_j=\frac{v(b+\theta_j)}{D}\ (j\in\{L,H\}),$$
--   $$p^D=\frac{v\big(2-\theta_H^2-\theta_L^2-b(\theta_H+\theta_L)\big)}{D},\qquad f^D_j=\frac{v(\theta_j-b)}{D}\ (j\in\{H,L\}),\qquad \Pi^D=\frac{v^2}{D},$$
--   where $p^D=P^D(N^D_B,N^D_L,N^D_H)$ and $f^D_j=F^D_j(N^D_B,N^D_j)$. The participation $N^D_j$ by type is footnote 15.
--
--   These closed forms are the discrimination side of every welfare comparison in Proposition 2.
--
--   **Formalization Note.** The optimum is a global maximizer of $\Pi^D$ over $\mathbb R^3$, written $(N_B,N_L,N_H)$ with the low type second and the high type third; existence is part of the statement.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), pp. 3345–3346, §4.2.2, displays (13)–(15); p. 3355, footnote 15

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem discrimination_equilibrium (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    (∃ y : ℝ × ℝ × ℝ, IsDiscrOpt v b θH θL y) ∧
    ∀ y : ℝ × ℝ × ℝ, IsDiscrOpt v b θH θL y →
      y.2.1 + y.2.2 = v * (2 * b + θL + θH) / Dden b θH θL ∧
      y.1 = 2 * v / Dden b θH θL ∧
      y.2.1 = v * (b + θL) / Dden b θH θL ∧
      y.2.2 = v * (b + θH) / Dden b θH θL ∧
      PD v b y.1 y.2.1 y.2.2 = v * (2 - θH ^ 2 - θL ^ 2 - b * (θH + θL)) / Dden b θH θL ∧
      FDH θH y.1 y.2.2 = v * (θH - b) / Dden b θH θL ∧
      FDL θL y.1 y.2.1 = v * (θL - b) / Dden b θH θL ∧
      profitD v b θH θL y = v ^ 2 / Dden b θH θL := by sorry

end TwoSidedPD.Baseline
