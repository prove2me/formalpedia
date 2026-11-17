-- Prove2me | Theorems.Thm_TwoStageRnQ_paper_rule_follows_rand
-- name    : TwoStageRnQ.paper_rule_follows_rand
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:22:05.024092+00:00
-- url     : https://prove2.me/theorems/ca648350-af02-4bb7-ad22-a7e9241d011d
-- title:
--   Every paper-compatible classical rule follows the rule with an outcome-dependent remainder
-- statement:
--   **Every paper-compatible classical rule belongs to the rule class with an outcome-dependent remainder.**
--   1. If a shipment policy $\pi$ runs the classical complete-lot rule with controls $(R_1,R_2,Q,n)$ from a compatible initialization in the sense of `RuleRand.PaperRnQAll` (no condition on the remainder), then $\pi$ satisfies `RuleRand.FollowsRnQRand` for $(R_1,R_2,Q,n)$, with remainder $\rho=W(0)\bmod Q$.
--   2. Every policy satisfying `Rule.FollowsRnQ` with controls $c=(R_1,R_2,Q,n,\rho)$ satisfies `RuleRand.FollowsRnQRand` for $(R_1,R_2,Q,n)$, with the constant remainder $\rho$.
--
--   **Formalization Note** The key step in part 1 is that the Stage-2 physical stock $W=IL_2-IP_1$ keeps its remainder modulo $Q$ for all $t\ge0$: upstream receipts add multiples of $nQ$ (including the initial pipeline) and downstream dispatches remove multiples of $Q$. With $W\ge0$ and the matching rule (a pending request implies $W<Q$) this gives $IP_1=\min\{\widehat{IP}_1,\,IL_2-\rho\}$ with $\widehat{IP}_1=IP_1+Q\beta$.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Section 4.1; Appendix A.2 (compatible initialization); Appendix A.3, Lemma A.2.

import Definitions.Def_TwoStageRnQ_RuleRand

namespace TwoStageRnQ

theorem paper_rule_follows_rand :
    (∀ (P : Params) (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 R2 : ℤ) (Q n : ℕ+),
      RuleRand.PaperRnQAll S π R1 R2 Q n → RuleRand.FollowsRnQRand S π R1 R2 Q n) ∧
    (∀ (P : Params) (S : DemandSpace P) (π : ShipmentPolicy P S) (c : ClassicalControls),
      Rule.FollowsRnQ S π c → RuleRand.FollowsRnQRand S π c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2.1) := by
  sorry

end TwoStageRnQ
