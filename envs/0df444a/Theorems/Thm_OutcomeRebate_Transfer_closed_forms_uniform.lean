-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_closed_forms_uniform
-- name    : OutcomeRebate.Transfer.closed_forms_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:19.82147+00:00
-- url     : https://prove2.me/theorems/45732744-87f6-4410-a95b-beb39b024d21
-- title:
--   §3.1.1–§3.1.2, pp. 14–15 (PDF 15–16) — uniform-pricing demand (n/v̄)(v̄ − β̄pz)⁺ and payer objective W^U_payer
-- statement:
--   Under uniform pricing, let $\bar\beta \in \{\beta,1\}$ and $p \ge 0$. The expected demand $N^U$ and the payer's objective $W^U_{\text{payer}} = \Pi^U_{\text{payer}} + \Pi^U_{\text{patient}}$ satisfy
--   $$N^U = \frac{n}{\bar v}\,(\bar v - \bar\beta p z)^+,$$
--   $$W^U_{\text{payer}} = \frac{n}{\bar v}\,(\bar v - \bar\beta p z)^+\Big[q v' - p + \frac q2(\bar v + \bar\beta p z)\Big].$$
--
--   Every later statement uses these closed forms of the integral model of demand and payoffs.
--
--   **Formalization Note** Demand is defined as $n/\bar v$ times the Lebesgue measure of the set of buyers in $[0,\bar v]$. The patient payoff is $n/\bar v$ times the integral over that set of $q(v-\bar\beta p) - (1-q)\bar\beta p$. The identities are statements about these definitions.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), pp. 14–15 (PDF 15–16), §3.1.1 (expected demand) and §3.1.2 (W^U_payer)

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Closed forms under uniform pricing (§3.1.1–§3.1.2, pp. 14–15). For `β̄ ∈ {β, 1}` and `p ≥ 0`:
the expected demand is `(n/v̄)(v̄ − β̄pz)⁺` and the payer objective is
`W^U_payer = (n/v̄)(v̄ − β̄pz)⁺ [qv′ − p + (q/2)(v̄ + β̄pz)]`. -/
theorem closed_forms_uniform (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    demandU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 ∧
      payerObjU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 *
        (P.q * P.vp - p + P.q / 2 * (P.vbar + bb * p * P.z)) := by sorry

end OutcomeRebate.Transfer
