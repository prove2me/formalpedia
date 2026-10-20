-- Prove2me | Theorems.Thm_SellingData_AppendsRotation_proposition7_appends_rotation
-- name    : SellingData.AppendsRotation.proposition7_appends_rotation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:19.747729+00:00
-- url     : https://prove2.me/theorems/c56147ab-36fb-4fc6-9743-660a187a4537
-- title:
--   Proposition 7, p. 20 — data appends, c_L < c_H < û: α*_H = α^e_H; α*_L < α^e_L if c_H < v⁺, α*_L > α^e_L if v⁺ < c_L
-- statement:
--   Consider the selling of data appends under the rotation-ordered information structure, with targeting costs $c_L<c_H<\hat u$ below the prior mean. Assume the regularity of footnote 5 ($k$ continuous on $[\underline\alpha,\bar\alpha]$, differentiable on $(\underline\alpha,\bar\alpha)$, $k'(\underline\alpha)=0$, $k'(\alpha)\to+\infty$ as $\alpha\to\bar\alpha^-$) and that $\partial H/\partial\alpha$ is jointly continuous on $[\underline v,\bar v]\times(0,1)$.
--
--   1. If $c_L<c_H<v^+$, then
--      - the informativeness levels offered to the high-cost type by optimal menus are exactly the efficient ones: a level $a$ is $\alpha_H$ of some optimal menu if and only if $a$ maximizes the benchmark (12) at $c_H$ ($\alpha^*_H=\alpha^e_H$);
--      - every optimal menu gives the low-cost type strictly less information than every efficient level at $c_L$:
--      $$
--      \alpha^*_L<\alpha^e_L .
--      $$
--   2. If $v^+<c_L<c_H$, then again $\alpha^*_H=\alpha^e_H$ in the same sense, and
--      $$
--      \alpha^*_L>\alpha^e_L
--      $$
--      for every optimal menu and every efficient level at $c_L$.
--
--   This is the general-distribution version of the "double reversal" relative to marketing lists: with data appends and costs below the prior mean, the high-cost marketers become the high type of the screening problem, so they are served efficiently, and the low-cost marketers' information is distorted, downward below the rotation point and upward above it.
--
--   **Formalization Note.** Optimal menus are maximizers of the full screening problem (6) with $IR_i: U_{ii}\ge\max\{\hat u-c_i,0\}$, fees $T\ge0$ and $\alpha\in[\underline\alpha,\bar\alpha]$; they are not defined through (15). "$\alpha^*_H=\alpha^e_H$" is equality of the two sets of maximizers. The first sentence of the proposition is stated only within the two cost ranges, where the constraints the paper drops in (15) are guaranteed to hold; for $c_L<v^+<c_H$ it is stated for (15) in a milestone. The branch $v^+<c_L<c_H<\hat u$ is empty when $v^+\ge\hat u$ (for example for symmetric structures, where $v^+=\hat u$), as on the page. The footnote-5 and continuity hypotheses are what make the comparisons strict: without them an efficient level can sit at an endpoint of $[\underline\alpha,\bar\alpha]$, where it can coincide with the optimal one.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 20, Proposition 7; proof p. 33

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_Setting

namespace SellingData.AppendsRotation

open Set

/-- Proposition 7, p. 20. In selling data appends with `c_L < c_H < û`:
if `c_H < v⁺` (so `c_L < c_H < v⁺`), the informativeness levels offered to the high-cost type by
optimal menus are exactly the efficient ones (`α*_H = α^e_H`), and every optimal menu gives the
low-cost type strictly less information than every efficient level (`α*_L < α^e_L`);
if `v⁺ < c_L` (so `v⁺ < c_L < c_H`), again `α*_H = α^e_H`, and `α*_L > α^e_L`. -/
theorem proposition7_appends_rotation (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous)
    (hcH : M.cH < M.uHat) :
    (M.cH < M.vPlus →
      (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αH = a) ↔ M.IsEfficient M.θ M.cH a) ∧
      (∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient (1 - M.θ) M.cL a → m.αL < a)) ∧
    (M.vPlus < M.cL →
      (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αH = a) ↔ M.IsEfficient M.θ M.cH a) ∧
      (∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient (1 - M.θ) M.cL a → a < m.αL)) := by sorry

end SellingData.AppendsRotation
