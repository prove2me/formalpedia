-- Prove2me | Theorems.Thm_SupplierAudit_Joint_lemma_OA11
-- name    : SupplierAudit.Joint.lemma_OA11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:47.508493+00:00
-- url     : https://prove2.me/theorems/8b438207-3c91-420c-8ea7-759207d47186
-- title:
--   Lemma OA11 — for $K<\tilde K$, auditing $S_1$ and $S_c$ beats auditing $S_c$ alone
-- statement:
--   Consider the joint-auditing coalition with competing buyers ($0<\beta\le1$), in the Sec. 4.3 scenario $\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M)$. Let $\Pi^b(e_{c1},e_{cc},e_{c2})$ be its aggregate expected profit, and let
--   $$\tilde K=\max_{(y,z)\in[0,1]^2}\Pi^b(y,z,0)\big|_{K=0}-\max_{y\in[0,1]}\Pi^b(0,y,0)\big|_{K=0}.$$
--   Then $\tilde K\ge0$. Moreover, if $0\le K<\tilde K$, there are efforts $y,z\in(0,1]$ such that
--   $$\Pi^b(0,y',0)<\Pi^b(y,z,0)\qquad\text{for every }y'\in(0,1].$$
--
--   In words: when the fixed cost is below $\tilde K$, some plan that audits both $S_1$ and the common supplier is strictly better than every plan that audits the common supplier alone.
--
--   **Formalization Note** "Jointly audit" means a positive effort on each audited supplier, so both sides of the comparison range over positive efforts ($(0,1]$), and each pays the fixed cost once per audited supplier. The threshold is the one defined in the paper's proof.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma OA11 and its proof, p. ec12 (PDF 40); scenario of Sec. 4.3, p. 13

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Lemma OA11, p. ec12: with `K̃` as defined in its proof, `K̃ ≥ 0`, and for `0 ≤ K < K̃` some joint
audit of `S₁` and `S_c` (both efforts positive) is strictly better than every joint audit of `S_c`
alone (positive effort). -/
theorem lemma_OA11 (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) :
    0 ≤ Ktilde P ∧
    ∀ K : ℝ, 0 ≤ K → K < Ktilde P →
      ∃ y ∈ Set.Ioc (0 : ℝ) 1, ∃ z ∈ Set.Ioc (0 : ℝ) 1, ∀ y' ∈ Set.Ioc (0 : ℝ) 1,
        aggProfit P K (0, y', 0) < aggProfit P K (y, z, 0) := by sorry

end SupplierAudit.Joint
