-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_purchase_rule_uniform
-- name    : OutcomeRebate.Transfer.purchase_rule_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:17.223779+00:00
-- url     : https://prove2.me/theorems/0ffaece2-2b34-4e70-964f-20bafac1c13d
-- title:
--   §3.1.1, p. 14 (PDF 15) — under uniform pricing a patient buys iff v ≥ β̄pz
-- statement:
--   Consider uniform pricing. Let $\bar\beta \in \{\beta, 1\}$ be the patient cost share, $p \ge 0$ the price and $v \ge 0$ a patient's value from treatment success. The patient's expected prospect-theory welfare from buying is
--   $$q\,u(v - \bar\beta p) + (1-q)\,u(-\bar\beta p),$$
--   which equals $q(v-\bar\beta p)^\alpha - (1-q)\lambda(\bar\beta p)^\alpha$ if $v \ge \bar\beta p$, and $-q\lambda(\bar\beta p - v)^\alpha - (1-q)\lambda(\bar\beta p)^\alpha$ otherwise. This welfare is non-negative if and only if
--   $$v \ \ge\ \bar\beta p z, \qquad z = 1 + \Big(\lambda\frac{1-q}{q}\Big)^{1/\alpha}.$$
--
--   The rule makes demand a threshold in $v$, and it is the source of the factor $z$ in every uniform-pricing formula.
--
--   **Formalization Note** The standing assumptions are those of the model. An indifferent patient (welfare exactly $0$) buys, matching the page's "if and only if $v \ge \bar\beta pz$".
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 14 (PDF 15), §3.1.1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Purchase rule under uniform pricing (§3.1.1, p. 14). For a cost share `β̄ ∈ {β, 1}`, a price
`p ≥ 0` and a value `v ≥ 0`, the patient buys (has non-negative expected welfare
`q·u(v − β̄p) + (1 − q)·u(−β̄p)`) iff `v ≥ β̄pz`. -/
theorem purchase_rule_uniform (P : Params) (hS : P.Standing) (bb p v : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ welfareU P bb p v ↔ bb * p * P.z ≤ v := by sorry

end OutcomeRebate.Transfer
