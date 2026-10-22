-- Prove2me | Theorems.Thm_TradeCreditIns_Cancelable_lemma_b1
-- name    : TradeCreditIns.Cancelable.lemma_b1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:40.884721+00:00
-- url     : https://prove2.me/theorems/82b26272-c729-4196-8a7d-df400f3dcbc1
-- title:
--   Lemma B.1 — incentive conditions for insurer monitoring
-- statement:
--   Let $\kappa=(p,\delta,f)$ be a cancelable contract in the three-signal model, and let $C_E$ be the insurer's expected cost if he monitors, including effort cost, claims, and refunds. He monitors exactly when the supplier would ship under coverage at the prior default probability $\bar\beta$ and
--
--   $$
--   C_E\le \bar\beta(r-\delta),\qquad C_E\le f.
--   $$
--
--   The first bound compares monitoring with keeping coverage without monitoring; the second compares it with canceling without monitoring. Because $f\le p$, these bounds also secure participation.
--
--   **Formalization Note** Signal 1 is index 0. $C_E$ is calculated from the actual cancelation and shipping decisions; its sum corresponds to the right sides of (13)–(14), with ties settled by (64)–(66). The paper's $c>0$ convention is included in the standing assumptions.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), p. 31 (PDF 32), Lemma B.1, equations (12)–(14); proof p. xi (PDF 43)

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

namespace TradeCreditIns.Cancelable

/-- Lemma B.1, p. 31 (PDF 32): monitoring against keeping, canceling,
and not participating, with the contract's tie rules. -/
theorem lemma_b1 (P : Params) (κ : Contract) (hS : P.Standing)
    (hκ : κ.IsCancelable P) :
    InsurerMonitors P κ ↔
      ShipsCovered P κ P.βbar ∧
      insurerCostEffort P κ ≤ P.βbar * (P.r - κ.δ) ∧
      insurerCostEffort P κ ≤ κ.f := by sorry

end TradeCreditIns.Cancelable
