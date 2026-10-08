-- Prove2me | Theorems.Thm_SupplierAudit_Competition_lemma_OA5
-- name    : SupplierAudit.Competition.lemma_OA5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:23.442789+00:00
-- url     : https://prove2.me/theorems/3544391d-ca53-454a-9d36-c9058462e9a7
-- title:
--   Lemma OA5 — both buyers audit their independent suppliers iff $K < K^M_u$
-- statement:
--   Assume the buyers compete, $\beta \in (0,1]$, and the interior-effort assumption $\hat e_I < 1$. Let $K^M_u$ be the threshold (OA-10). Then:
--
--   1. for every fixed cost $0 \le K < K^M_u$, the profile in which each buyer audits his independent supplier with effort $e^*_I$ (eq. (1)), $\big((e^*_I,0),(e^*_I,0)\big)$, is an equilibrium;
--   2. for every $K \ge K^M_u$, no profile $\big((x,0),(y,0)\big)$ with $x, y > 0$, in which each buyer audits his independent supplier, is an equilibrium.
--
--   This is the first of the three ingredients of Proposition 2: the "both audit independent suppliers" equilibrium exists exactly below $K^M_u$.
--
--   **Formalization Note** The paper says "there exists a threshold $K^M_u$"; the statement uses the threshold the proof defines in (OA-10), which is stronger. Equilibria follow the paper's tie-breaking rule. The interior-effort assumption of p. 10 is encoded as $\hat e_I < 1$.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma OA5 and (OA-10), p. ec8 (PDF 36)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem lemma_OA5 (P : Params) (hβ : 0 < P.β) (hint : eHatI P < 1) :
    (∀ K : ℝ, 0 ≤ K → K < KMu P → IsEquilibrium P K (eStarI P, 0) (eStarI P, 0)) ∧
    (∀ K : ℝ, KMu P ≤ K → ∀ x y : ℝ, 0 < x → 0 < y → ¬ IsEquilibrium P K (x, 0) (y, 0)) := by sorry

end SupplierAudit.Competition
