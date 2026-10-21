-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_equation_1
-- name    : PostTradeFees.Welfare.equation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:06.266621+00:00
-- url     : https://prove2.me/theorems/7a692bec-34ee-4d09-bdc9-d2a9a2ee4b9e
-- title:
--   Equation (1), p. 9 (PDF 10) — optimal limit-order quotes satisfy the indifference system
-- statement:
--   Fix $N>1$ brokers, valuations $V_h>V_l\ge0$, a cross-broker post-trade cost $c>0$ and a fee structure $k$ (uniform or trade-specific). Let $(V_b,V_s)$ be a stationary equilibrium: $V_b$ is the greatest expected profit of a buyer posting a bid when the seller's value of posting her own limit order is $V_s$, and symmetrically for $V_s$.
--
--   1. Let $B$ be an optimal bid and $A$ an optimal ask that both attract counterparties at every broker (the "all" strategy). Write $fee$ for the fee per leg of a cross-broker trade and $E(fee)=\frac1N fee_{\mathrm{in}}+\frac{N-1}{N}fee$ for the expected fee per leg. Then, with $\gamma=\tfrac12$,
--   $$
--   B-V_l-fee=\gamma\,[A-V_l-E(fee)],\qquad V_h-A-fee=\gamma\,[V_h-B-E(fee)].
--   $$
--   2. Under trade-specific fees, let $B$ and $A$ be optimal quotes that attract only same-broker counterparties (the "own" strategy). Then the same system holds with $fee=E(fee)=0$ and $\gamma=\frac1{2N}$:
--   $$
--   B-V_l=\tfrac1{2N}\,(A-V_l),\qquad V_h-A=\tfrac1{2N}\,(V_h-B).
--   $$
--
--   The left-hand sides are the counterparty's gain from hitting the quote with a market order; the right-hand sides are the value of posting her own limit order instead. Optimal quotes leave the marginal counterparty exactly indifferent, and this system is the paper's solution method for the quotes of Equations (2)–(4).
--
--   **Formalization Note** The system is stated as a property of every optimal quote of the given type at every model equilibrium, not as a definition of the quotes. Under uniform fees the internal and cross-broker fees coincide, so $fee=E(fee)=\frac{N-1}{N}c$; under trade-specific fees $fee=c$ and $E(fee)=\frac{N-1}{N}c$, as on pp. 10 and 12.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), p. 9 (PDF 10), §4, Equation (1); values of fee, E(fee), γ from p. 10 (PDF 11) and p. 12 (PDF 13)

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Equation (1): optimal limit-order quotes satisfy the indifference system. Under "all",
`fee` is the cross-broker fee, `E(fee)` the expected fee and `γ = 1/2`; under "own" with
trade-specific fees, `fee = E(fee) = 0` and `γ = 1/(2N)`. -/
theorem equation_1 (P : Params) (hS : P.Standing) (k : FeeStructure) (Vb Vs : ℝ)
    (hE : IsEquilibrium P k Vb Vs) :
    (∀ B A,
      bidProfit P k Vs B = Vb →
      SellerHits P k true Vs B → SellerHits P k false Vs B →
      askProfit P k Vb A = Vs →
      BuyerHits P k true Vb A → BuyerHits P k false Vb A →
      B - P.Vl - fee P k false = (1 / 2 : ℝ) * (A - P.Vl - expectedFee P k) ∧
      P.Vh - A - fee P k false = (1 / 2 : ℝ) * (P.Vh - B - expectedFee P k)) ∧
    (k = .tradeSpecific → ∀ B A,
      bidProfit P k Vs B = Vb →
      SellerHits P k true Vs B → ¬ SellerHits P k false Vs B →
      askProfit P k Vb A = Vs →
      BuyerHits P k true Vb A → ¬ BuyerHits P k false Vb A →
      B - P.Vl - 0 = 1 / (2 * (P.N : ℝ)) * (A - P.Vl - 0) ∧
      P.Vh - A - 0 = 1 / (2 * (P.N : ℝ)) * (P.Vh - B - 0)) := by sorry

end PostTradeFees.Welfare
