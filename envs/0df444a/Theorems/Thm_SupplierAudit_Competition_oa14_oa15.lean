-- Prove2me | Theorems.Thm_SupplierAudit_Competition_oa14_oa15
-- name    : SupplierAudit.Competition.oa14_oa15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:12.822401+00:00
-- url     : https://prove2.me/theorems/2227445d-d664-4cfd-8d26-a013227f21eb
-- title:
--   (OA-14), (OA-15) — the gain from auditing and the best response decrease in $e_{22}$; $\hat e_I > e^*_I$
-- statement:
--   Assume the buyers compete, $\beta \in (0,1]$. Then:
--
--   1. for every $e_{11} \in (0,1]$, buyer $B_1$'s gain from auditing $S_1$ with effort $e_{11}$ rather than auditing nothing,
--   $$e_{22} \mapsto \Pi^b_1(e_{11},0;e_{22},0)\big|_{K=0} - \Pi^b_1(0,0;e_{22},0),$$
--   is strictly decreasing on $[0,1]$ (the rival's effort on his own supplier makes auditing less valuable, (OA-14));
--   2. the best-response function $e^*_{11}(e_{22})$ of (OA-9) is strictly decreasing;
--   3. consequently $\hat e_I > e^*_I$ (OA-15).
--
--   These monotonicity facts are what order the three thresholds in Lemma OA7.
--
--   **Formalization Note** The page displays the two derivatives; only their sign is stated here. The printed derivative of $e^*_{11}(e_{22})$ omits a factor $1/a$; the sign is unaffected.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), proof of Lemma OA7, (OA-14), (OA-15), p. ec10 (PDF 38)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem oa14_oa15 (P : Params) (hβ : 0 < P.β) :
    (∀ e11 ∈ Set.Ioc (0 : ℝ) 1,
      StrictAntiOn (fun e22 => expProfit₁ P 0 e11 0 e22 0 - expProfit₁ P 0 0 0 e22 0)
        (Set.Icc (0 : ℝ) 1)) ∧
    StrictAnti (bestResp P) ∧
    eStarI P < eHatI P := by sorry

end SupplierAudit.Competition
