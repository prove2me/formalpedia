-- Prove2me | Theorems.Thm_TradeCreditIns_Cancelable_upper_bound
-- name    : TradeCreditIns.Cancelable.upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:40.892709+00:00
-- url     : https://prove2.me/theorems/1aec1be2-cdf9-47ea-9730-a160532da281
-- title:
--   Proof of Proposition 3 — first-best bounds every participating contract
-- statement:
--   In the three-signal model, let $\kappa$ be any cancelable contract under which the insurer monitors. The supplier's expected payoff under $\kappa$ cannot exceed the centralized planner's first-best payoff:
--
--   $$
--   \Pi_S(\kappa)\le\Pi^{FB}.
--   $$
--
--   This is the upper bound behind the proof's assertion that $\Pi_2$ is the highest possible supplier payoff; it applies across all cancelation and shipping patterns, not just the pattern of the proposed contract.
--
--   **Formalization Note** Signal 1 is index 0. Monitoring includes the insurer's participation condition, and financing cost is nonnegative under the disclosed $l\ge0$ assumption. Decisions use the tie rules in the proof of Proposition 3.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), proof of Proposition 3, p. xi (PDF 43), 'the highest possible supplier payoff'

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

namespace TradeCreditIns.Cancelable

/-- The “highest possible supplier payoff” assertion in the proof of
Proposition 3, p. xi (PDF 43). -/
theorem upper_bound (P : Params) (hS : P.Standing) :
    ∀ κ : Contract, κ.IsCancelable P →
      InsurerMonitors P κ → supplierPayoff P κ ≤ firstBest P := by sorry

end TradeCreditIns.Cancelable
