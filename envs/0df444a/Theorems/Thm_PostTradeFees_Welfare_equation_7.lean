-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_equation_7
-- name    : PostTradeFees.Welfare.equation_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:04.231523+00:00
-- url     : https://prove2.me/theorems/9abccaf9-1a9f-4b74-805a-3d237210f2b7
-- title:
--   Equation (7), p. 15 (PDF 16) — trading rates, internalization rates and welfare of the all and own chains
-- statement:
--   Fix $N>1$, $V_h>V_l\ge0$ and $c>0$. Let $\varphi_{all}$ be a stationary distribution of the "all" order-flow chain (A1) and $\varphi_{own}$ one of the "own" chain (A2), on the states 0 = limit order, 1 = internalized market order, 2 = non-internalized market order. Define the trading rate $TR=\varphi_1+\varphi_2$, the internalization rate $IR=\varphi_1/(\varphi_1+\varphi_2)$, and expected welfare per period $W=\varphi_1(V_h-V_l)+\varphi_2(V_h-V_l-2c)$. Then
--   $$
--   TR^*_{k,all}=\frac13,\quad IR^*_{k,all}=\frac1N,\quad TR^*_{TS,own}=\frac1{2N+1},\quad IR^*_{TS,own}=1,
--   $$
--   $$
--   W^*_{k,all}=\frac13\Big[V_h-V_l-2c\,\frac{N-1}{N}\Big],\qquad W^*_{TS,own}=\frac1{2N+1}\,[V_h-V_l],
--   $$
--   and for both chains welfare agrees with Equation (6), $W=TR\,[V_h-V_l-2c\,(1-IR)]$.
--
--   These are the long-run welfare levels that Corollary 3 compares.
--
--   **Formalization Note** Welfare is defined from the stationary distribution (internalized trades realize $V_h-V_l$, cross-broker trades $V_h-V_l-2c$); the closed forms above are conclusions, not definitions.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), p. 15 (PDF 16), Equation (7); Equation (6), p. 14 (PDF 15)

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Equation (7), with Equation (6): trading rates, internalization rates and welfare of
the stationary distributions of the "all" and "own" order-flow chains. -/
theorem equation_7 (P : Params) (hS : P.Standing)
    (φa φo : Fin 3 → ℝ)
    (hφa : MarkovChain.IsStationary (chainAll P.N) φa)
    (hφo : MarkovChain.IsStationary (chainOwn P.N) φo) :
    tradingRate φa = 1 / 3 ∧
    internalizationRate φa = 1 / (P.N : ℝ) ∧
    tradingRate φo = 1 / (2 * (P.N : ℝ) + 1) ∧
    internalizationRate φo = 1 ∧
    welfare P φa =
      (1 / 3 : ℝ) * (P.Vh - P.Vl - 2 * P.c * (((P.N : ℝ) - 1) / (P.N : ℝ))) ∧
    welfare P φo = (1 / (2 * (P.N : ℝ) + 1)) * (P.Vh - P.Vl) ∧
    welfare P φa =
      tradingRate φa * (P.Vh - P.Vl - 2 * P.c * (1 - internalizationRate φa)) ∧
    welfare P φo =
      tradingRate φo * (P.Vh - P.Vl - 2 * P.c * (1 - internalizationRate φo)) := by sorry

end PostTradeFees.Welfare
