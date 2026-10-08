-- Prove2me | Theorems.Thm_SupplierAudit_Joint_eq3_cost_shares
-- name    : SupplierAudit.Joint.eq3_cost_shares
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:37.623349+00:00
-- url     : https://prove2.me/theorems/674fe1f4-5b53-48f7-971e-116e9e4128fa
-- title:
--   Eq. (3) — the cost shares $\Gamma_1,\Gamma_2$ split the auditing cost and equalize the buyers' profits
-- statement:
--   For a joint plan $x=(e_{c1},e_{cc},e_{c2})$ and fixed cost $K$, let $C(x)=\sum_{j\in\{1,c,2\}}\big[K\mathbf 1\{e_{cj}>0\}+\tfrac a2e_{cj}^2\big]$ be its total auditing cost. Let $R^b_i(x)$ be buyer $B_i$'s expected profit excluding auditing costs, and $\Delta\Pi=R^b_1(x)-R^b_2(x)$. The cost shares
--   $$\Gamma_1=\tfrac12\big[C(x)+\Delta\Pi\big],\qquad \Gamma_2=\tfrac12\big[C(x)-\Delta\Pi\big]$$
--   satisfy
--   $$\Gamma_1+\Gamma_2=C(x),\qquad R^b_1(x)-\Gamma_1=R^b_2(x)-\Gamma_2=\tfrac12\,\Pi^b(x),$$
--   where $\Pi^b(x)$ is the coalition's aggregate profit. If $e_{c2}=0$, then
--   $$\Gamma_1=\frac12\Big[\sum_{j=1,c}\Big[K\mathbf 1\{e_{cj}>0\}+\frac a2e_{cj}^2\Big]+\Delta\Pi\Big],\qquad \Gamma_2=\frac12\Big[\sum_{j=1,c}\Big[K\mathbf 1\{e_{cj}>0\}+\frac a2e_{cj}^2\Big]-\Delta\Pi\Big],$$
--   which are the formulas (3) of Proposition 3.
--
--   These are the two fairness conditions of the paper's proof: the shares pay the whole cost and leave both buyers the same expected profit. They pin down what "fair share" means in Proposition 3.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), eq. (3), p. 14; proof of Proposition 3, part (1), p. ec13 (PDF 41)

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Proof of Proposition 3, part (1), p. ec13, and eq. (3), p. 14: the shares `Γ₁, Γ₂` split the
total auditing cost and leave both buyers the same expected profit, half the coalition's aggregate
profit; when `S₂` is not audited they are the printed formulas (3). -/
theorem eq3_cost_shares (P : SupplierAudit.Competition.Params) (K : ℝ) (x : ℝ × ℝ × ℝ) :
    Gamma₁ P K x + Gamma₂ P K x = totalCost P K x ∧
    jointG₁ P x - Gamma₁ P K x = jointG₂ P x - Gamma₂ P K x ∧
    jointG₁ P x - Gamma₁ P K x = aggProfit P K x / 2 ∧
    (x.2.2 = 0 →
      Gamma₁ P K x = (1 / 2) * ((SupplierAudit.Competition.auditCost P K x.1 + SupplierAudit.Competition.auditCost P K x.2.1) + deltaPi P x) ∧
      Gamma₂ P K x = (1 / 2) * ((SupplierAudit.Competition.auditCost P K x.1 + SupplierAudit.Competition.auditCost P K x.2.1) - deltaPi P x)) := by sorry

end SupplierAudit.Joint
