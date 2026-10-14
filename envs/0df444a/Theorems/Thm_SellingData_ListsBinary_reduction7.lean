-- Prove2me | Theorems.Thm_SellingData_ListsBinary_reduction7
-- name    : SellingData.ListsBinary.reduction7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:52.59246+00:00
-- url     : https://prove2.me/theorems/5df7f0e2-7c2c-4a08-bf61-74524f3403f3
-- title:
--   Equation (7), p. 11 — with IR_H and IC_{L,H} binding, the screening problem (6) reduces to (7)
-- statement:
--   In the screening problem (6) of *Selling Data to Marketers* for marketing lists, write $\mathrm{pay}(\alpha,c)=\sigma_h(\alpha)[v_h(\alpha)-c]$, so that $U_{ij}=-T_j+\mathrm{pay}(\alpha_j,c_i)$, and let
--   $$\Pi^{(7)}(\alpha_H,\alpha_L)=\theta\big[\sigma_h(\alpha_H)[v_h(\alpha_H)-c_H]-k(\alpha_H)\big]+(1-\theta)\big[\sigma_h(\alpha_L)[v_h(\alpha_L)-c_L]-\sigma_h(\alpha_H)(c_H-c_L)-k(\alpha_L)\big]$$
--   be the objective of (7). Then:
--   1. every feasible menu $(T_H,\alpha_H,T_L,\alpha_L)$ has expected profit $\Pi\le\Pi^{(7)}(\alpha_H,\alpha_L)$;
--   2. if $(\alpha_H,\alpha_L)$ maximizes $\Pi^{(7)}$ over $[\underline\alpha,\bar\alpha]^2$, then the menu with $T_H=\mathrm{pay}(\alpha_H,c_H)$ (IR$_H$ binding) and $T_L=T_H+\mathrm{pay}(\alpha_L,c_L)-\mathrm{pay}(\alpha_H,c_L)$ (IC$_{L,H}$ binding) is feasible for (6), including $T_L\ge0$, IR$_L$ and IC$_{H,L}$;
--   3. if $k$ is continuous on $[\underline\alpha,\bar\alpha]$, a menu is optimal for (6) if and only if it is feasible, $U_{HH}=0$, $U_{LL}=U_{LH}$, and $(\alpha_H,\alpha_L)$ maximizes $\Pi^{(7)}$ over $[\underline\alpha,\bar\alpha]^2$.
--
--   Together these say that substituting the binding IR$_H$ and IC$_{L,H}$ constraints into (6) yields the problem (7) without loss: the dropped constraints hold automatically at its solutions.
--
--   **Formalization Note** Part 3 needs continuity of $k$ only to guarantee that (7) attains its maximum; parts 1 and 2 hold for every $k$ of the model.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 11, (6)–(7)

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsBinary

/-- Reduction (7), p. 11: (i) every feasible menu earns at most the objective (7) at its own
informativeness levels; (ii) at every maximizer of (7) the menu with binding `IR_H` and
`IC_{L,H}` is feasible for (6); (iii) if `k` is continuous on `[α̲, ᾱ]`, a menu is optimal
for (6) iff it is feasible, `IR_H` and `IC_{L,H}` bind, and its informativeness pair
maximizes (7). -/
theorem reduction7 (S : Screening) :
    (∀ m : Menu, S.Feasible m → S.profit m ≤ S.reducedProfit m.αH m.αL) ∧
    (∀ αH αL : ℝ, S.IsReducedMaximizer αH αL →
      S.Feasible
        { TH := S.payoff αH S.cH, αH := αH,
          TL := S.payoff αH S.cH + S.payoff αL S.cL - S.payoff αH S.cL, αL := αL }) ∧
    (ContinuousOn S.k (Set.Icc S.aLo S.aHi) →
      ∀ m : Menu, S.IsOptimalMenu m ↔
        (S.Feasible m ∧ S.U m .H .H = 0 ∧ S.U m .L .L = S.U m .L .H ∧
          S.IsReducedMaximizer m.αH m.αL)) := by sorry

end SellingData.ListsBinary
