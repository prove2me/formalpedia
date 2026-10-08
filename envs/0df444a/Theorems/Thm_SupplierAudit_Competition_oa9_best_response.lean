-- Prove2me | Theorems.Thm_SupplierAudit_Competition_oa9_best_response
-- name    : SupplierAudit.Competition.oa9_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:39.494887+00:00
-- url     : https://prove2.me/theorems/036d5570-5091-4834-bb34-32f4b7298332
-- title:
--   (OA-9) — $B_1$'s best-response effort $e^*_{11}(e_{22})$; $e^*_I$ and $\hat e_I$ as its values
-- statement:
--   Assume the buyers compete, $\beta \in (0,1]$, and let $e^*_{11}(e_{22})$ be the right-hand side of (OA-9). Then:
--
--   1. for every $e_{22} \in [0,1]$ with $e^*_{11}(e_{22}) \in [0,1]$, the effort $e^*_{11}(e_{22})$ is the unique maximizer over $[0,1]$ of $B_1$'s expected profit when $B_1$ audits only $S_1$ and $B_2$ audits only $S_2$ with effort $e_{22}$, at $K = 0$:
--   $$\Pi^b_1(x,0;e_{22},0)\big|_{K=0} < \Pi^b_1(e^*_{11}(e_{22}),0;e_{22},0)\big|_{K=0}\quad\text{for all } x \in [0,1],\ x \ne e^*_{11}(e_{22});$$
--   2. $e^*_I$ of eq. (1) is the symmetric solution of the system of best responses: $e^*_{11}(e^*_I) = e^*_I$;
--   3. $\hat e_I$ of eq. (2) is the best response to no audit: $e^*_{11}(0) = \hat e_I$.
--
--   These are the facts that turn the closed forms (1) and (2) into equilibrium efforts in Lemmas OA5 and OA6.
--
--   **Formalization Note** For $e_{11} > 0$ the fixed cost $K$ shifts $\Pi^b_1(e_{11},0;e_{22},0)$ by the constant $-K$, so the maximizer over $(0,1]$ does not depend on $K$; the comparison with no audit is the content of the thresholds.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), proof of Lemma OA5, (OA-9), p. ec8 (PDF 36); ê_I = e*_11(0), p. ec9–ec10 (PDF 37–38)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem oa9_best_response (P : Params) (hβ : 0 < P.β) :
    (∀ e22 ∈ Set.Icc (0 : ℝ) 1, bestResp P e22 ∈ Set.Icc (0 : ℝ) 1 →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ bestResp P e22 →
        expProfit₁ P 0 x 0 e22 0 < expProfit₁ P 0 (bestResp P e22) 0 e22 0) ∧
    bestResp P (eStarI P) = eStarI P ∧
    bestResp P 0 = eHatI P := by sorry

end SupplierAudit.Competition
