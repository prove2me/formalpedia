-- Prove2me | Theorems.Thm_SellingData_AppendsBinary_reduction_eq8
-- name    : SellingData.AppendsBinary.reduction_eq8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:49.552783+00:00
-- url     : https://prove2.me/theorems/888e85de-6192-475d-a8a9-64a14a14f3f6
-- title:
--   (8), p. 13 — with c_L < c_H < û, IR_L and IC_{H,L} bind and the data-append screening problem reduces to (8)
-- statement:
--   Consider the data-append screening problem with costs $c_L<c_H<\hat u$, and write $\Pi^{(8)}(\alpha_H,\alpha_L)$ for the objective of (8),
--   $$\Pi^{(8)}=\theta\big[\sigma_h(\alpha_H)[v_h(\alpha_H)-c_H]-\sigma_h(\alpha_L)(c_L-c_H)-k(\alpha_H)\big]+(1-\theta)\big[\sigma_h(\alpha_L)[v_h(\alpha_L)-c_L]-k(\alpha_L)\big]-\hat u+c_L .$$
--   Then:
--
--   1. every feasible menu $(T_H,\alpha_H,T_L,\alpha_L)$ has profit at most $\Pi^{(8)}(\alpha_H,\alpha_L)$;
--   2. for every maximizer $(\alpha_H,\alpha_L)$ of $\Pi^{(8)}$ over $[\underline\alpha,\bar\alpha]^2$, the menu in which $IR_L$ and $IC_{H,L}$ bind is feasible (it also satisfies $IR_H$, $IC_{L,H}$ and $T_H,T_L\ge 0$) and its profit equals $\Pi^{(8)}(\alpha_H,\alpha_L)$;
--   3. if $k$ is continuous on $[\underline\alpha,\bar\alpha]$, a menu is optimal for the data-append problem if and only if it is feasible, $U_{LL}=U_{L0}$ and $U_{HH}=U_{HL}$, and its pair $(\alpha_H,\alpha_L)$ maximizes $\Pi^{(8)}$ over $[\underline\alpha,\bar\alpha]^2$.
--
--   This is the reduction behind Proposition 3: it says that the seller's problem with data appends is equivalent to the unconstrained maximization (8), in which only the low type's participation and the high type's incentive constraint are kept.
--
--   **Formalization Note** The page only says that the binding constraints are $IR_L$ and $IC_{H,L}$ and substitutes them; parts 1 and 2 make explicit that the dropped constraints ($IR_H$, $IC_{L,H}$, nonnegative fees) hold at every maximizer of (8). Continuity of $k$ in part 3 only guarantees that (8) has a maximizer.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 13, §3.2, (8)

import Mathlib
import Definitions.Def_SellingData_AppendsBinary_Setting

namespace SellingData.AppendsBinary

open Model

/-- (8), p. 13: when `c_L < c_H < û`, the data-append screening problem reduces to (8).
(i) Every feasible menu earns at most the value of (8) at its informativeness pair.
(ii) At every maximizer of (8) over `[α̲, ᾱ]²`, the menu with `IR_L` and `IC_{H,L}` binding is
feasible and earns exactly that value.
(iii) If `k` is continuous on `[α̲, ᾱ]`, a menu is optimal for the data-append problem iff it is
feasible, `IR_L` and `IC_{H,L}` bind, and its informativeness pair maximizes (8). -/
theorem reduction_eq8 (M : Model) (hcH : M.cH < M.uHat) :
    (∀ m : Menu, M.Feasible m → M.profit m ≤ M.reducedProfit m.αH m.αL) ∧
      (∀ αH αL : ℝ, M.IsReducedMax αH αL →
        M.Feasible (M.bindingMenu αH αL) ∧
          M.profit (M.bindingMenu αH αL) = M.reducedProfit αH αL) ∧
      (ContinuousOn M.k (Set.Icc M.aLo M.aHi) →
        ∀ m : Menu, M.IsOptimalMenu m ↔
          (M.Feasible m ∧ M.U m SellingData.ListsBinary.CostType.L SellingData.ListsBinary.CostType.L = M.outside M.cL ∧
            M.U m SellingData.ListsBinary.CostType.H SellingData.ListsBinary.CostType.H = M.U m SellingData.ListsBinary.CostType.H SellingData.ListsBinary.CostType.L ∧
            M.IsReducedMax m.αH m.αL)) := by sorry

end SellingData.AppendsBinary
