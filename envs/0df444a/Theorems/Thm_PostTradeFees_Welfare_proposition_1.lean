-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_proposition_1
-- name    : PostTradeFees.Welfare.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:09.411285+00:00
-- url     : https://prove2.me/theorems/e5815fd6-4965-4662-8118-fd45c549cd6e
-- title:
--   Proposition 1, p. 11 (PDF 12) — uniform fees induce all-broker trading or no trading
-- statement:
--   Let $N>1$, $V_h>V_l\ge0$, and $c>0$. Under the uniform fee, a stationary equilibrium exists. In every such equilibrium, traders use the "all" strategy through the threshold
--
--   $$
--   c_U=\frac{N(V_h-V_l)}{2(N-1)}.
--   $$
--
--   The optimal all-broker bid and ask are those of Equation (2), and their observed and cumulative-fee spreads equal its stated formulas. For $c>c_U$, all optimal quotes attract no market order, so trading stops.
--
--   This classifies the uniform-fee market and supplies one of the strategy choices used in the welfare comparison.
--
--   **Formalization Note** Equilibrium means attained greatest limit-order profit on both sides; the inclusive boundary follows the paper's broadest-counterparty tie-break.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), p. 11 (PDF 12), Proposition 1; p. 10 (PDF 11), Equation (2)

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Proposition 1, uniform fees: all-broker trading until the no-trade threshold. -/
theorem proposition_1 (P : Params) (hS : P.Standing) :
    (∃ Vb Vs, IsEquilibrium P .uniform Vb Vs) ∧
    (∀ Vb Vs, IsEquilibrium P .uniform Vb Vs →
      (P.c ≤ cU P →
        PlaysAll P .uniform Vb Vs ∧
        (∀ B, bidProfit P .uniform Vs B = Vb →
          SellerHits P .uniform true Vs B →
          SellerHits P .uniform false Vs B → B = BstarUall P) ∧
        (∀ A, askProfit P .uniform Vb A = Vs →
          BuyerHits P .uniform true Vb A →
          BuyerHits P .uniform false Vb A → A = AstarUall P) ∧
        observedSpread (AstarUall P) (BstarUall P) =
          (P.Vh - P.Vl) / 3 - 2 * ((P.N : ℝ) - 1) * P.c / (3 * (P.N : ℝ)) ∧
        cumSpread P .uniform true (AstarUall P) (BstarUall P) =
          (P.Vh - P.Vl) / 3 + 4 * ((P.N : ℝ) - 1) * P.c / (3 * (P.N : ℝ))) ∧
      (cU P < P.c → RefrainsFromTrading P .uniform Vb Vs)) := by sorry

end PostTradeFees.Welfare
