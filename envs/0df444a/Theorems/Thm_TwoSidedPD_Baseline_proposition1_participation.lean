-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_proposition1_participation
-- name    : TwoSidedPD.Baseline.proposition1_participation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:06.007981+00:00
-- url     : https://prove2.me/theorems/14acee55-b05b-40ca-b201-84763fd9e1bd
-- title:
--   Proposition 1, p. 3344 — under price discrimination the equilibrium numbers of buyers and of sellers both increase
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1. Let $(N^U_B,N^U_S)$ be any maximizer of the uniform-pricing profit $\Pi^U$ and $(N^D_B,N^D_L,N^D_H)$ any maximizer of the discriminatory profit $\Pi^D$. Then
--   $$N^U_B<N^D_B\qquad\text{and}\qquad N^U_S<N^D_L+N^D_H .$$
--
--   In words: under price discrimination, the equilibrium number of both buyers and sellers increases compared with uniform pricing. This is the paper's first main result, and the buyer part of Proposition 2(i) is its corollary.
--
--   **Formalization Note.** The statement quantifies over all optima; their existence is the content of the two equilibrium milestones (displays (12) and (13)–(15)).
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3344, §4.1.3, Proposition 1 (proof: App. A.1, pp. 3351–3352)

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem proposition1_participation (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      x.1 < y.1 ∧ x.2 < y.2.1 + y.2.2 := by sorry

end TwoSidedPD.Baseline
