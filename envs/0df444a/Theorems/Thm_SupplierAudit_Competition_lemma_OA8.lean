-- Prove2me | Theorems.Thm_SupplierAudit_Competition_lemma_OA8
-- name    : SupplierAudit.Competition.lemma_OA8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:08.080993+00:00
-- url     : https://prove2.me/theorems/57d0171c-a17b-4c09-b68c-85412459628d
-- title:
--   Lemma OA8 — no equilibrium audits the common supplier
-- statement:
--   Assume the buyers compete, $\beta \in (0,1]$, and $\hat e_I < 1$. For every fixed cost $K \ge 0$, no profile in which some buyer puts positive effort on the common supplier $S_c$ is an equilibrium. In particular none of the following can be sustained in equilibrium: (a) one buyer audits his independent supplier and the other audits the common supplier; (b) both buyers audit the common supplier; (c) one buyer audits the common supplier and the other audits no supplier.
--
--   Together with Lemmas OA5 and OA6 this leaves only the profiles that appear in Proposition 2.
--
--   **Formalization Note** The three cases (a)–(c) are stated at once: a strategy audits at most one supplier, so a profile with positive effort on $S_c$ is of type (a), (b) or (c). The paper omits the proof ("similar to those of Lemmas OA5 and OA6").
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma OA8, p. ec10 (PDF 38)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem lemma_OA8 (P : Params) (hβ : 0 < P.β) (hint : eHatI P < 1) (K : ℝ) (hK : 0 ≤ K)
    (s₁ s₂ : ℝ × ℝ) (hc : 0 < s₁.2 ∨ 0 < s₂.2) :
    ¬ IsEquilibrium P K s₁ s₂ := by sorry

end SupplierAudit.Competition
