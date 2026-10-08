-- Prove2me | Theorems.Thm_SupplierAudit_Joint_aggProfit_displays
-- name    : SupplierAudit.Joint.aggProfit_displays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:23.849987+00:00
-- url     : https://prove2.me/theorems/5cc70019-9291-4ef5-bad9-fb8e5287036f
-- title:
--   Proofs of Lemmas OA9–OA10 — the coalition's profit $\Pi^b$ as a sum of the buyers' unilateral profits
-- statement:
--   Let $\Pi^b(e_{c1},e_{cc},e_{c2})$ be the joint-auditing coalition's aggregate expected profit, and $\Pi^b_1(e_{11},e_{1c};e_{22},e_{2c})$, $\Pi^b_2(e_{22},e_{2c};e_{11},e_{1c})$ the buyers' unilateral expected profits (each net of the buyer's own auditing costs). For every fixed cost $K$ and all efforts $y,z$,
--   $$\begin{aligned}
--   \Pi^b(0,y,0)&=\Pi^b_1(0,y;0,0)+\Pi^b_2(0,0;0,y),\\
--   \Pi^b(y,0,0)&=\Pi^b_1(y,0;0,0)+\Pi^b_2(0,0;y,0),\\
--   \Pi^b(y,z,0)&=\Pi^b_1(y,0;0,z)+\Pi^b_2(0,z;y,0),\\
--   \Pi^b(y,0,z)&=\Pi^b_1(y,0;z,0)+\Pi^b_2(z,0;y,0).
--   \end{aligned}$$
--
--   The coalition's profit for a joint plan therefore equals the sum of the buyers' unilateral profits when the audits of the plan are distributed between them, one supplier per buyer: auditing in a coalition changes who pays, not what is earned. In particular, each audited supplier's cost is incurred once. These are the expressions the paper uses in the proofs of Lemmas OA9 and OA10.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), proof of Lemma OA9, p. ec11 (PDF 39); proof of Lemma OA10, pp. ec11–ec12 (PDF 39–40)

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Proofs of Lemmas OA9 and OA10, pp. ec11–ec12: the coalition's aggregate expected profit is the
sum of the two buyers' unilateral expected profits at the corresponding efforts, with each audited
supplier's cost charged once. -/
theorem aggProfit_displays (P : SupplierAudit.Competition.Params) (K y z : ℝ) :
    aggProfit P K (0, y, 0) = expProfit₁ P K 0 y 0 0 + expProfit₂ P K 0 0 0 y ∧
    aggProfit P K (y, 0, 0) = expProfit₁ P K y 0 0 0 + expProfit₂ P K 0 0 y 0 ∧
    aggProfit P K (y, z, 0) = expProfit₁ P K y 0 0 z + expProfit₂ P K 0 z y 0 ∧
    aggProfit P K (y, 0, z) = expProfit₁ P K y 0 z 0 + expProfit₂ P K z 0 y 0 := by sorry

end SupplierAudit.Joint
