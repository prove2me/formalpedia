-- Prove2me | Theorems.Thm_TradeCreditIns_Cancelable_proposition_1
-- name    : TradeCreditIns.Cancelable.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:38.760777+00:00
-- url     : https://prove2.me/theorems/59f8f818-9c90-43d8-aa38-d2c45560023a
-- title:
--   Proposition 1 — potential value of trade credit insurance
-- statement:
--   Let $\bar\beta$ be the prior default probability, $L(0)$ the financing cost at zero cash flow, and $\phi=\sum_i\theta_i[r_0-(1-\beta_i)r]^+$ the value of canceling a shipment after monitoring. Under the paper's standing assumptions and Assumption 1, the first-best payoff $\Pi^{FB}$ and its increase over the no-insurance payoff $\Pi^{NI}$ satisfy
--
--   $$
--   \Pi^{FB}=(1-\bar\beta)r+(\phi-c)^+,
--   $$
--
--   $$
--   \Pi^{FB}-\Pi^{NI}
--     =\min\{\bar\beta L(0),(1-\bar\beta)r-r_0\}+(\phi-c)^+.
--   $$
--
--   The second identity is the paper's potential value of trade credit insurance. The first identifies the centralized benchmark used to define full value in Proposition 3.
--
--   **Formalization Note** Signal 1 is index 0. The first-best is independently defined as the maximum over the planner's possible policies; this theorem identifies its closed form.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), p. 11 (PDF 12), Proposition 1; proof p. ii (PDF 34), equations (20)–(21)

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

namespace TradeCreditIns.Cancelable

/-- Proposition 1, p. 11 (PDF 12), and first-best formula (20), p. ii (PDF 34). -/
theorem proposition_1 (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) :
    firstBest P = (1 - P.βbar) * P.r + max (φ P - P.c) 0 ∧
    firstBest P - noInsurance P =
      min (P.βbar * L P 0) ((1 - P.βbar) * P.r - P.r0) +
        max (φ P - P.c) 0 := by sorry

end TradeCreditIns.Cancelable
