-- Prove2me | Theorems.Thm_SupplierAudit_Competition_oa11_common_dominated
-- name    : SupplierAudit.Competition.oa11_common_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:07.834886+00:00
-- url     : https://prove2.me/theorems/6e868eb8-d8d7-4839-92b2-517c71392fe2
-- title:
--   (OA-11) — auditing $S_c$ is beaten by auditing $S_1$ with the same effort
-- statement:
--   Assume the buyers compete, $\beta \in (0,1]$. For every fixed cost $K$, every effort $e_1 \in (0,1]$ and every effort $e_2 \in [0,1]$ of buyer $B_2$ on his independent supplier,
--
--   $$\Pi^b_1(e_1,0;e_2,0) - \Pi^b_1(0,e_1;e_2,0) > 0 .$$
--
--   When the rival audits his independent supplier (or nobody), a buyer who audits the common supplier would do strictly better auditing his own independent supplier with the same effort: an audit of $S_c$ also protects the competitor. This is how the common supplier is excluded from the equilibria of Proposition 2.
--
--   **Formalization Note** Only the conclusion of (OA-11) is stated. The page's closed-form evaluation of the difference has a misprint: the prefactor of its second term should be $\beta(\hat w - w)$, not $\beta(d_M + \hat w - w)$; the sign of the difference is unaffected. Both sides pay the same audit cost, so the difference does not depend on $K$.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), proof of Lemma OA5 (b), (OA-11), p. ec8 (PDF 36) and p. ec9 (PDF 37)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem oa11_common_dominated (P : Params) (hβ : 0 < P.β) (K e₁ e₂ : ℝ)
    (h₁ : e₁ ∈ Set.Ioc (0 : ℝ) 1) (h₂ : e₂ ∈ Set.Icc (0 : ℝ) 1) :
    0 < expProfit₁ P K e₁ 0 e₂ 0 - expProfit₁ P K 0 e₁ e₂ 0 := by sorry

end SupplierAudit.Competition
