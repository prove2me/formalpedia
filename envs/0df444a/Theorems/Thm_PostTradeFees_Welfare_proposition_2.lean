-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_proposition_2
-- name    : PostTradeFees.Welfare.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:03.786636+00:00
-- url     : https://prove2.me/theorems/e1cd9b5b-7225-4112-a7ca-50d837bc2fdc
-- title:
--   Proposition 2, p. 13 (PDF 14) — trade-specific fees switch from all to own at c₁
-- statement:
--   Let $N>1$, $V_h>V_l\ge0$, and $c>0$. Under trade-specific fees, a stationary equilibrium exists. Every equilibrium uses the "all" strategy for
--
--   $$
--   c\le c_1=\frac{2N(N-1)(V_h-V_l)}{(2N+1)(2N-1)},
--   $$
--
--   with the quotes, observed spread, internalized and cross-broker cumulative-fee spreads, and average cumulative-fee spread of Equation (3). For $c>c_1$, it uses the "own" strategy, with the quotes and equal observed and cumulative-fee spreads of Equation (4).
--
--   This identifies the privately chosen trading regime under trade-specific fees.
--
--   **Formalization Note** Strategy selection is read from optimal quotes and market-order decisions; it is not defined by the threshold. Equality selects "all" as specified on p. 9.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), p. 13 (PDF 14), Proposition 2 and Equation (5); p. 12 (PDF 13), Equations (3)–(4)

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Proposition 2, trade-specific fees: all-broker trading through c₁, own-broker thereafter. -/
theorem proposition_2 (P : Params) (hS : P.Standing) :
    (∃ Vb Vs, IsEquilibrium P .tradeSpecific Vb Vs) ∧
    (∀ Vb Vs, IsEquilibrium P .tradeSpecific Vb Vs →
      (P.c ≤ c1 P →
        PlaysAll P .tradeSpecific Vb Vs ∧
        (∀ B, bidProfit P .tradeSpecific Vs B = Vb →
          SellerHits P .tradeSpecific true Vs B →
          SellerHits P .tradeSpecific false Vs B → B = BstarTSall P) ∧
        (∀ A, askProfit P .tradeSpecific Vb A = Vs →
          BuyerHits P .tradeSpecific true Vb A →
          BuyerHits P .tradeSpecific false Vb A → A = AstarTSall P) ∧
        observedSpread (AstarTSall P) (BstarTSall P) =
          (P.Vh - P.Vl) / 3 - 2 * ((P.N : ℝ) + 1) * P.c / (3 * (P.N : ℝ)) ∧
        cumSpread P .tradeSpecific true (AstarTSall P) (BstarTSall P) =
          observedSpread (AstarTSall P) (BstarTSall P) ∧
        cumSpread P .tradeSpecific false (AstarTSall P) (BstarTSall P) =
          observedSpread (AstarTSall P) (BstarTSall P) + 2 * P.c ∧
        averageCumSpread P .tradeSpecific (AstarTSall P) (BstarTSall P) =
          observedSpread (AstarTSall P) (BstarTSall P) +
            2 * ((P.N : ℝ) - 1) * P.c / (P.N : ℝ)) ∧
      (c1 P < P.c →
        PlaysOwn P .tradeSpecific Vb Vs ∧
        (∀ B, bidProfit P .tradeSpecific Vs B = Vb →
          SellerHits P .tradeSpecific true Vs B →
          ¬ SellerHits P .tradeSpecific false Vs B → B = BstarTSown P) ∧
        (∀ A, askProfit P .tradeSpecific Vb A = Vs →
          BuyerHits P .tradeSpecific true Vb A →
          ¬ BuyerHits P .tradeSpecific false Vb A → A = AstarTSown P) ∧
        observedSpread (AstarTSown P) (BstarTSown P) =
          ((2 * (P.N : ℝ) - 1) / (2 * (P.N : ℝ) + 1)) * (P.Vh - P.Vl) ∧
        cumSpread P .tradeSpecific true (AstarTSown P) (BstarTSown P) =
          observedSpread (AstarTSown P) (BstarTSown P))) := by sorry

end PostTradeFees.Welfare
