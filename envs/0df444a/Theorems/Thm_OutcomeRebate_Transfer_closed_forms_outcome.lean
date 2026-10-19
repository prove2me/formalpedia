-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_closed_forms_outcome
-- name    : OutcomeRebate.Transfer.closed_forms_outcome
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:24.453981+00:00
-- url     : https://prove2.me/theorems/9aaaa719-ed7a-4fcd-817e-f6339f20ef0e
-- title:
--   §3.2.1–§3.2.2, p. 18 (PDF 19) — outcome-based demand (n/v̄)(v̄ − β̄p)⁺ and payer objective W^O_payer
-- statement:
--   Under outcome-based pricing, let $\bar\beta \in \{\beta,1\}$ and $p \ge 0$. The expected demand $N^O$ and the payer's objective $W^O_{\text{payer}} = \Pi^O_{\text{payer}} + \Pi^O_{\text{patient}}$ satisfy
--   $$N^O = \frac{n}{\bar v}\,(\bar v - \bar\beta p)^+,$$
--   $$W^O_{\text{payer}} = \frac{nq}{\bar v}\,(\bar v - \bar\beta p)^+\Big(v' - p + \frac{\bar v + \bar\beta p}{2}\Big).$$
--
--   These are the outcome-based counterparts of the uniform closed forms.
--
--   **Formalization Note** As for uniform pricing, demand and patient payoff are a Lebesgue measure and a set integral over the buyers in $[0,\bar v]$.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 18 (PDF 19), §3.2.1 (expected demand) and §3.2.2 (W^O_payer)

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Closed forms under outcome-based pricing (§3.2.1–§3.2.2, p. 18). For `β̄ ∈ {β, 1}` and `p ≥ 0`:
the expected demand is `(n/v̄)(v̄ − β̄p)⁺` and the payer objective is
`W^O_payer = (nq/v̄)(v̄ − β̄p)⁺ (v′ − p + (v̄ + β̄p)/2)`. -/
theorem closed_forms_outcome (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    demandO P bb p = P.n / P.vbar * max (P.vbar - bb * p) 0 ∧
      payerObjO P bb p = P.n * P.q / P.vbar * max (P.vbar - bb * p) 0 *
        (P.vp - p + (P.vbar + bb * p) / 2) := by sorry

end OutcomeRebate.Transfer
