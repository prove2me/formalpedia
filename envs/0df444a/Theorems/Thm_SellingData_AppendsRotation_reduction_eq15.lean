-- Prove2me | Theorems.Thm_SellingData_AppendsRotation_reduction_eq15
-- name    : SellingData.AppendsRotation.reduction_eq15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:09.081513+00:00
-- url     : https://prove2.me/theorems/cfc3b560-aa64-4dbf-b6bb-abbad50ce97c
-- title:
--   (15), p. 20 — with c_L < c_H < û, binding IR_L and IC_{H,L} reduce the data-append screening problem to (15)
-- statement:
--   Consider the data-append screening problem with $c_L<c_H<\hat u$, and write $\Pi(\alpha_H,\alpha_L)$ for the objective (15) and $P(\alpha,c)=\int_c^{\bar v}(v-c)\,dH(v,\alpha)$.
--
--   1. Every feasible menu $(T_H,\alpha_H),(T_L,\alpha_L)$ earns at most $\Pi(\alpha_H,\alpha_L)$:
--   $$
--   \theta\,[T_H-k(\alpha_H)]+(1-\theta)\,[T_L-k(\alpha_L)]\le \Pi(\alpha_H,\alpha_L).
--   $$
--   2. If moreover $c_H<v^+$ or $v^+<c_L$, let $(\alpha_H,\alpha_L)$ be any maximizer of $\Pi$ over $[\underline\alpha,\bar\alpha]^2$ and set the fees that make $IR_L$ and $IC_{H,L}$ bind,
--   $$
--   T_L=P(\alpha_L,c_L)-(\hat u-c_L),\qquad T_H=T_L+P(\alpha_H,c_H)-P(\alpha_L,c_H).
--   $$
--   Then the menu $(T_H,\alpha_H),(T_L,\alpha_L)$ is feasible (all four constraints and $T_H,T_L\ge0$ hold) and its profit equals $\Pi(\alpha_H,\alpha_L)$.
--
--   Together, the two parts say that, on the two cost ranges, the optimal menus of the data-append problem are exactly the binding completions of the maximizers of (15).
--
--   **Formalization Note.** The paper substitutes the binding constraints without checking that the dropped constraints $IR_H$ and $IC_{L,H}$ hold at the maximizer of (15). $IC_{L,H}$ holds there when the informativeness levels are ordered as the costs relative to $v^+$ dictate, which is guaranteed when both costs lie on the same side of $v^+$; part 2 is therefore stated for $c_H<v^+$ or $v^+<c_L$. The "+" missing between the brackets of (15) on p. 20 is restored.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 20, §4.2, (15)

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_Setting

namespace SellingData.AppendsRotation

open Set

/-- Reduction (15), p. 20. Let `c_L < c_H < û`.
(i) Every feasible menu of the data-append screening problem earns at most the value of (15) at its
own informativeness levels.
(ii) If moreover `c_H < v⁺` or `v⁺ < c_L`, then every maximizer `(α_H, α_L)` of (15) over
`[α̲, ᾱ]²`, completed with the fees that make `IR_L` and `IC_{H,L}` bind,
`T_L = ∫_{c_L}^{v̄}(v − c_L)dH(v, α_L) − (û − c_L)` and
`T_H = T_L + ∫_{c_H}^{v̄}(v − c_H)dH(v, α_H) − ∫_{c_H}^{v̄}(v − c_H)dH(v, α_L)`,
is a feasible menu whose profit equals the value of (15). -/
theorem reduction_eq15 (M : Model) (hcH : M.cH < M.uHat) :
    (∀ m : Menu, M.Feasible m → M.profit m ≤ M.reducedProfit m.αH m.αL) ∧
    (M.cH < M.vPlus ∨ M.vPlus < M.cL →
      ∀ αH αL : ℝ, M.IsReducedOptimal αH αL →
        let TL := M.payoff αL M.cL - (M.uHat - M.cL)
        let TH := TL + M.payoff αH M.cH - M.payoff αL M.cH
        M.Feasible ⟨TH, αH, TL, αL⟩ ∧
          M.profit ⟨TH, αH, TL, αL⟩ = M.reducedProfit αH αL) := by sorry

end SellingData.AppendsRotation
