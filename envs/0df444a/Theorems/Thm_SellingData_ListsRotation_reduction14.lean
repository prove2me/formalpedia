-- Prove2me | Theorems.Thm_SellingData_ListsRotation_reduction14
-- name    : SellingData.ListsRotation.reduction14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:59.573976+00:00
-- url     : https://prove2.me/theorems/7c2fdede-97e4-46a8-95de-3938479879e9
-- title:
--   (14), p. 18 — binding $IR_H$ and $IC_{L,H}$ reduce the screening problem (6) with payoff (13) to (14)
-- statement:
--   Consider the screening problem (6) with the payoff $U_{ij}=-T_j+\int_{c_i}^{\bar v}(v-c_i)\,dH(v,\alpha_j)$ of (13), and the reduced objective
--   $$\Pi^{(14)}(\alpha_H,\alpha_L)=\theta\Big[P(\alpha_H,c_H)-k(\alpha_H)\Big]+(1-\theta)\Big[P(\alpha_L,c_L)-P(\alpha_H,c_L)+P(\alpha_H,c_H)-k(\alpha_L)\Big],$$
--   where $P(\alpha,c)=\int_c^{\bar v}(v-c)\,dH(v,\alpha)$. Then:
--
--   1. every feasible menu $(T_H,\alpha_H,T_L,\alpha_L)$ earns at most $\Pi^{(14)}(\alpha_H,\alpha_L)$;
--   2. for every maximizer $(\alpha_H,\alpha_L)$ of $\Pi^{(14)}$ over $[\underline\alpha,\bar\alpha]^2$, the menu with binding $IR_H$ and $IC_{L,H}$,
--   $$T_H=P(\alpha_H,c_H),\qquad T_L=T_H+P(\alpha_L,c_L)-P(\alpha_H,c_L),$$
--   is feasible for (6), and its profit equals $\Pi^{(14)}(\alpha_H,\alpha_L)$.
--
--   Together the two parts say that the screening problem (6) has the same value as (14) and is solved by substituting the binding constraints.
--
--   **Formalization Note** The paper drops the constraints $IR_L$, $IC_{H,L}$ and $T_j\ge0$ without comment; part 2 asserts that they hold at every maximizer of (14), for all cost levels allowed by the model ($\underline v<c_L<c_H<\bar v$).
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 18, (13)–(14) and the paragraph between them

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Reduction (14), p. 18: (i) every feasible menu of (6) (with payoff (13)) earns at most the
objective (14) at its own informativeness levels; (ii) at every maximizer of (14) the menu with
binding `IR_H` and `IC_{L,H}` is feasible for (6) and earns the value of (14). -/
theorem reduction14 (M : Model) :
    (∀ m : Menu, M.Feasible m → M.profit m ≤ M.reducedProfit m.αH m.αL) ∧
    (∀ αH αL : ℝ, M.IsReducedMax αH αL →
      M.Feasible
          { TH := M.payoff αH M.cH, αH := αH,
            TL := M.payoff αH M.cH + M.payoff αL M.cL - M.payoff αH M.cL, αL := αL } ∧
        M.profit
            { TH := M.payoff αH M.cH, αH := αH,
              TL := M.payoff αH M.cH + M.payoff αL M.cL - M.payoff αH M.cL, αL := αL } =
          M.reducedProfit αH αL) := by sorry

end SellingData.ListsRotation
