-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_equation_5
-- name    : PostTradeFees.Welfare.equation_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:04.457668+00:00
-- url     : https://prove2.me/theorems/9ca60c1b-99e1-45af-9d89-e9c6b0238ded
-- title:
--   Equation (5), p. 13 (PDF 14) — the all-strategy LO profit is at least the own-strategy profit iff c ≤ c₁
-- statement:
--   Fix $N>1$, $V_h>V_l\ge0$ and $c>0$, and consider trade-specific fees (zero for an internalized trade, $c$ per leg for a cross-broker trade). Let
--   $$
--   B^*_{TS,all}=\frac{V_h+2V_l}{3}+\frac{(N+1)c}{3N},\qquad B^*_{TS,own}=\frac{V_h+2V_lN}{2N+1}
--   $$
--   be the bids of Equations (3) and (4). The limit-order profit of the "all" strategy is $\tfrac12\,[V_h-B^*_{TS,all}-E(fee)]$ with $E(fee)=\frac{N-1}{N}c$, and that of the "own" strategy is $\frac1{2N}\,[V_h-B^*_{TS,own}]$. Then
--   $$
--   \tfrac12\,[V_h-B^*_{TS,all}-E(fee)]\ \ge\ \tfrac1{2N}\,[V_h-B^*_{TS,own}]
--   \iff c\le c_1\equiv\frac{2N(N-1)(V_h-V_l)}{(2N+1)(2N-1)},
--   $$
--   and the two profits are equal exactly when $c=c_1$.
--
--   The threshold $c_1$ is where limit-order traders switch from targeting every broker to targeting only their own broker under trade-specific fees (Proposition 2).
--
--   **Formalization Note** The profits are the paper's closed forms evaluated at the closed-form bids; the equilibrium content of the switch is Proposition 2. The weak inequality reflects the tie-break that an indifferent trader plays "all".
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), p. 13 (PDF 14), Equation (5); bids from p. 12 (PDF 13), Equations (3)–(4)

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Equation (5): under trade-specific fees the LO profit of the "all" strategy,
`γ (V_h - B*_{TS,all} - E(fee))` with `γ = 1/2`, `E(fee) = ((N-1)/N) c`, is at least the
LO profit of the "own" strategy, `(1/(2N)) (V_h - B*_{TS,own})`, exactly when `c ≤ c₁`,
and the two are equal exactly at `c = c₁`. -/
theorem equation_5 (P : Params) (hS : P.Standing) :
    ((1 / (2 * (P.N : ℝ))) * (P.Vh - BstarTSown P) ≤
        (1 / 2 : ℝ) * (P.Vh - BstarTSall P - expectedFee P .tradeSpecific) ↔
      P.c ≤ c1 P) ∧
    ((1 / 2 : ℝ) * (P.Vh - BstarTSall P - expectedFee P .tradeSpecific) =
        (1 / (2 * (P.N : ℝ))) * (P.Vh - BstarTSown P) ↔
      P.c = c1 P) := by sorry

end PostTradeFees.Welfare
