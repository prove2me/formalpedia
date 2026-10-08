-- Prove2me | Theorems.Thm_SupplierAudit_Joint_prop3_thresholds
-- name    : SupplierAudit.Joint.prop3_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:58.263976+00:00
-- url     : https://prove2.me/theorems/4bcdb00b-78c0-4c03-9cf9-2febd43d68e0
-- title:
--   Proof of Prop. 3, part (2) — the coalition's optimal audit set for $K<K^L_c$, $K^L_c\le K<K^H_c$, $K\ge K^H_c$
-- statement:
--   Consider the joint-auditing coalition with competing buyers ($0<\beta\le1$), in the Sec. 4.3 scenario $\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M)$. Let $\hat K$ and $\tilde K$ be the thresholds of Lemmas OA9 and OA11, and set
--   $$K^L_c=\min\Big\{\frac{\hat K+\tilde K}{2},\tilde K\Big\},\qquad K^H_c=\max\Big\{\frac{\hat K+\tilde K}{2},\hat K\Big\}.$$
--   Feasible joint plans $(e_{c1},e_{cc},e_{c2})\in[0,1]^3$ audit at most two suppliers. For every fixed cost $K\ge0$:
--
--   1. if $K<K^L_c$, some maximizer of the coalition's aggregate profit over the feasible plans has $e_{c1}>0$, $e_{cc}>0$, $e_{c2}=0$, and at it $\Delta\Pi>0$;
--   2. if $K^L_c\le K<K^H_c$, some maximizer has $e_{c1}=0$, $e_{cc}>0$, $e_{c2}=0$, and at it $\Delta\Pi=0$;
--   3. if $K\ge K^H_c$, the plan that audits no supplier is a maximizer.
--
--   This is the structural half of Proposition 3, with the thresholds given explicitly.
--
--   **Formalization Note** "Yields the highest aggregate profit" is read as "some maximizer has this pattern". The proof compares candidate plans by weak inequalities, so uniqueness of the maximizer is not claimed. The paper's convention that $S_1$ (not $S_2$) is the audited independent supplier is the choice of the maximizer in case 1: its mirror image, which audits $S_2$ and $S_c$, has $\Delta\Pi<0$.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), proof of Proposition 3, part (2), pp. ec13–ec14 (PDF 41–42); Proposition 3, pp. 13–14

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Proof of Proposition 3, part (2), p. ec13: with `K^L_c = min{(K̂+K̃)/2, K̃}` and
`K^H_c = max{(K̂+K̃)/2, K̂}`, the coalition's optimal plan audits `S₁` and `S_c` (with `∆Π > 0`) for
`K < K^L_c`, only `S_c` (with `∆Π = 0`) for `K^L_c ≤ K < K^H_c`, and no supplier for `K ≥ K^H_c`. -/
theorem prop3_thresholds (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) (K : ℝ) (hK : 0 ≤ K) :
    (K < KcL P → ∃ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x ∧
        0 < x.1 ∧ 0 < x.2.1 ∧ x.2.2 = 0 ∧ 0 < deltaPi P x) ∧
    (KcL P ≤ K → K < KcH P → ∃ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x ∧
        x.1 = 0 ∧ 0 < x.2.1 ∧ x.2.2 = 0 ∧ deltaPi P x = 0) ∧
    (KcH P ≤ K → IsMaxOn (aggProfit P K) Feasible (0, 0, 0)) := by sorry

end SupplierAudit.Joint
