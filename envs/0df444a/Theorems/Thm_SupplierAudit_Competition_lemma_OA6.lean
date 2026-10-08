-- Prove2me | Theorems.Thm_SupplierAudit_Competition_lemma_OA6
-- name    : SupplierAudit.Competition.lemma_OA6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:58.257596+00:00
-- url     : https://prove2.me/theorems/3f233612-b874-4af6-8394-b3e031720583
-- title:
--   Lemma OA6 — one buyer audits his independent supplier and the other none iff $K^L_u \le K < K^H_u$
-- statement:
--   Assume the buyers compete, $\beta \in (0,1]$, and $\hat e_I < 1$. Let $K^L_u$ and $K^H_u$ be the thresholds (OA-12) and (OA-13). Then:
--
--   1. for every fixed cost $K \ge 0$ with $K^L_u \le K < K^H_u$, both profiles $\big((\hat e_I,0),(0,0)\big)$ and $\big((0,0),(\hat e_I,0)\big)$, in which one buyer audits his independent supplier with effort $\hat e_I$ (eq. (2)) and the other audits nothing, are equilibria;
--   2. for every $K \ge 0$ with $K < K^L_u$ or $K \ge K^H_u$, no profile $\big((x,0),(0,0)\big)$ or $\big((0,0),(x,0)\big)$ with $x > 0$ is an equilibrium.
--
--   This is the second ingredient of Proposition 2: the asymmetric equilibria exist exactly on $[K^L_u, K^H_u)$.
--
--   **Formalization Note** The paper's "there exist thresholds" is stated with the thresholds the proof defines. Equilibria follow the tie-breaking rule of p. 10; $\hat e_I < 1$ encodes the interior-effort assumption.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma OA6, (OA-12), (OA-13), p. ec9 (PDF 37)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem lemma_OA6 (P : Params) (hβ : 0 < P.β) (hint : eHatI P < 1) :
    (∀ K : ℝ, 0 ≤ K → KLu P ≤ K → K < KHu P →
      IsEquilibrium P K (eHatI P, 0) (0, 0) ∧ IsEquilibrium P K (0, 0) (eHatI P, 0)) ∧
    (∀ K : ℝ, 0 ≤ K → (K < KLu P ∨ KHu P ≤ K) → ∀ x : ℝ, 0 < x →
      ¬ IsEquilibrium P K (x, 0) (0, 0) ∧ ¬ IsEquilibrium P K (0, 0) (x, 0)) := by sorry

end SupplierAudit.Competition
