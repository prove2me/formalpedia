-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_proposition_3_part_3
-- name    : OutcomeRebate.Transfer.proposition_3_part_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:07.865422+00:00
-- url     : https://prove2.me/theorems/883405f8-7146-4f09-abe4-b15c005acb07
-- title:
--   Proposition 3 part 3, p. 21 (PDF 22) — the firm profits more under outcome-based pricing iff q < q0
-- statement:
--   Suppose Assumptions 1 and 2 hold, and let $p^U$, $p^O$ be equilibrium prices under uniform and outcome-based pricing. Then the firm's profit difference is
--   $$\Pi^O_{\text{firm}}(p^O;\beta) - \Pi^U_{\text{firm}}(p^U;\beta) = \frac{n}{4\bar v\beta}\,(qz - 1)\Big(\frac{\bar v^2}{z} - \frac{c^2\beta^2}{q}\Big),$$
--   and the firm's expected profit is strictly higher under outcome-based pricing if and only if the drug is high-risk, $q < q_0$.
--
--   The firm has an incentive to adopt outcome-based pricing exactly for high-risk drugs.
--
--   **Formalization Note** The closed-form difference is the display in the paper's proof (p. 54), included as part of the statement. Profits are the firm's realized profits at the equilibrium prices, each evaluated at the payer's coverage response.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 21 (PDF 22), Proposition 3 part 3; identity from its proof, p. 54 (PDF 55)

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Proposition 3 part 3 (p. 21), with the identity of its proof (p. 54). Under Assumption 2, at the
equilibrium prices `p^U`, `p^O`:
`Π^O_firm − Π^U_firm = (n/(4v̄β))(qz − 1)(v̄²/z − c²β²/q)`, and the firm's expected profit is higher
under outcome-based pricing iff the drug is high-risk (`q < q₀`). -/
theorem proposition_3_part_3 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    realizedProfitO P pO - realizedProfitU P pU =
        P.n / (4 * P.vbar * P.β) * (P.q * P.z - 1) *
          (P.vbar ^ 2 / P.z - P.c ^ 2 * P.β ^ 2 / P.q) ∧
      (realizedProfitU P pU < realizedProfitO P pO ↔ P.q < q0 P.α P.lam) := by sorry

end OutcomeRebate.Transfer
