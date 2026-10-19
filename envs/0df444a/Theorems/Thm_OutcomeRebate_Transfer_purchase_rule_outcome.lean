-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_purchase_rule_outcome
-- name    : OutcomeRebate.Transfer.purchase_rule_outcome
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:22.93327+00:00
-- url     : https://prove2.me/theorems/2fb56222-4072-45b9-8674-28317b21c3f4
-- title:
--   §3.2.1, p. 18 (PDF 19) — under outcome-based pricing a patient buys iff v ≥ β̄p
-- statement:
--   Consider outcome-based pricing, where the patient pays only if the treatment succeeds. Let $\bar\beta \in \{\beta, 1\}$, $p \ge 0$ and $v \ge 0$. The patient's expected welfare from buying is
--   $$q\,u(v - \bar\beta p),$$
--   which is $q(v - \bar\beta p)^\alpha$ if $v \ge \bar\beta p$ and $-q\lambda(\bar\beta p - v)^\alpha$ otherwise. It is non-negative if and only if
--   $$v \ \ge\ \bar\beta p.$$
--
--   Risk sensitivity and loss aversion therefore play no role in the purchase decision under outcome-based pricing.
--
--   **Formalization Note** An indifferent patient buys, as on the page.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 18 (PDF 19), §3.2.1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Purchase rule under outcome-based pricing (§3.2.1, p. 18). For a cost share `β̄ ∈ {β, 1}`, a price
`p ≥ 0` and a value `v ≥ 0`, the patient buys (has non-negative expected welfare `q·u(v − β̄p)`)
iff `v ≥ β̄p`. -/
theorem purchase_rule_outcome (P : Params) (hS : P.Standing) (bb p v : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ welfareO P bb p v ↔ bb * p ≤ v := by sorry

end OutcomeRebate.Transfer
