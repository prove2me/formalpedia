-- Prove2me | Theorems.Thm_SellingData_ListsRotation_proposition5_lists_rotation
-- name    : SellingData.ListsRotation.proposition5_lists_rotation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:45.921607+00:00
-- url     : https://prove2.me/theorems/06ab5492-97c6-4582-9e59-71312de48e71
-- title:
--   Proposition 5, p. 18 — marketing lists, rotation order: $\alpha^*_L=\alpha^e_L$; $\alpha^*_H>\alpha^e_H$ if $c_L<c_H<v^+$, $\alpha^*_H<\alpha^e_H$ if $v^+<c_L<c_H$
-- statement:
--   In the rotation-order model of selling marketing lists, assume the footnote-5 conditions on the selling cost $k$ (continuous on $[\underline\alpha,\bar\alpha]$, differentiable on $(\underline\alpha,\bar\alpha)$, $k'(\underline\alpha)=0$ from the right, $k'(\alpha)\to+\infty$ as $\alpha\to\bar\alpha^-$) and that $\partial H/\partial\alpha$ is jointly continuous on $[\underline v,\bar v]\times(0,1)$. Call a menu optimal if it solves the screening problem (6) with the payoff (13), and call $a$ efficient for type $i$ if it maximizes the benchmark (12) for $c_i$.
--
--   1. The low-cost plans of optimal menus are exactly the efficient levels for $c_L$: $a$ is the $\alpha_L$ of some optimal menu if and only if $a$ is efficient for $c_L$ (that is, $\alpha^*_L=\alpha^e_L$).
--   2. If $c_L<c_H<v^+$, every optimal menu provides the high-cost marketers more information than the benchmark: $\alpha^e_H<\alpha^*_H$ for every optimal menu and every efficient level $\alpha^e_H$ for $c_H$.
--   3. If $v^+<c_L<c_H$, every optimal menu provides the high-cost marketers less information: $\alpha^*_H<\alpha^e_H$.
--
--   In short, the low type of the screening problem (the low-cost marketer) receives efficient information, while the information sold to the high-cost marketer is distorted upward when both costs lie below the rotation point and downward when both lie above it.
--
--   **Formalization Note** "The optimal" and "the efficient" informativeness need not be unique (no convexity of $k$ is assumed), so the statement is about sets of maximizers. As on the page, $\alpha^*_L=\alpha^e_L$ is stated for the screening problem (6) with no condition on the position of the costs relative to $v^+$. The footnote-5 conditions and the continuity of $\partial H/\partial\alpha$ are pinned for the existence of optimal menus and for the strict inequalities; the paper says footnote 5's conditions are standard but unnecessary for its results.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 18, Proposition 5; proof pp. 32–33

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Proposition 5, p. 18 (proof pp. 32–33). (1) The low-cost plans of optimal menus of (6) (with
payoff (13)) are exactly the efficient levels for `c_L` (`α*_L = α^e_L`); (2) if `c_L < c_H < v⁺`
(resp. `v⁺ < c_L < c_H`), the high-cost plan of every optimal menu is strictly above (resp. below)
every efficient level for `c_H` (`α*_H > α^e_H`, resp. `α*_H < α^e_H`).
Under the footnote-5 conditions on `k` and joint continuity of `∂H/∂α`. -/
theorem proposition5_lists_rotation (M : Model) (hk : M.Footnote5) (hHα : M.HαContinuous) :
    (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αL = a) ↔ M.IsEfficient (1 - M.θ) M.cL a) ∧
    (M.cL < M.cH ∧ M.cH < M.vPlus →
      ∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient M.θ M.cH a → a < m.αH) ∧
    (M.vPlus < M.cL ∧ M.cL < M.cH →
      ∀ m : Menu, M.IsOptimalMenu m → ∀ a : ℝ, M.IsEfficient M.θ M.cH a → m.αH < a) := by sorry

end SellingData.ListsRotation
