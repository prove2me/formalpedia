-- Prove2me | Theorems.Thm_SupplierAudit_Competition_proposition_2
-- name    : SupplierAudit.Competition.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:19.748916+00:00
-- url     : https://prove2.me/theorems/4875721f-c3ef-4614-858e-053748db9113
-- title:
--   Proposition 2 — unilateral auditing decisions when the buyers compete
-- statement:
--   Consider the auditing game with competing buyers, $\beta \in (0,1]$, under the standing assumptions of the model and the interior-effort assumption $\hat e_I < 1$. Let $e^*_I$ and $\hat e_I$ be given by eqs. (1) and (2). There exist thresholds $K^L_u < K^M_u < K^H_u$ such that, for every fixed audit cost $K \ge 0$:
--
--   1. if $K < K^L_u$, the unique equilibrium is $\big((e^*_I,0),(e^*_I,0)\big)$: each buyer audits only his independent supplier, with effort $e^*_I$;
--   2. if $K^L_u \le K < K^M_u$, the equilibria are exactly $\big((e^*_I,0),(e^*_I,0)\big)$, $\big((\hat e_I,0),(0,0)\big)$ and $\big((0,0),(\hat e_I,0)\big)$: either each buyer audits his independent supplier with effort $e^*_I$, or one buyer audits his independent supplier with effort $\hat e_I$ and the other audits none of his suppliers;
--   3. if $K^M_u \le K < K^H_u$, the equilibria are exactly $\big((\hat e_I,0),(0,0)\big)$ and $\big((0,0),(\hat e_I,0)\big)$;
--   4. if $K \ge K^H_u$, the unique equilibrium is $\big((0,0),(0,0)\big)$: neither buyer audits any supplier.
--
--   Here a profile lists $(e_{11},e_{1c})$ and $(e_{22},e_{2c})$. In every case the common supplier, the one with the higher centrality, receives zero auditing effort: under downstream competition an audit of the common supplier would let the rival free-ride.
--
--   **Formalization Note** "Unique equilibrium" means the equilibrium set is a singleton, and "two types of equilibria" means the set consists of exactly the three listed profiles ("one buyer … the other …" covers both labellings). The ordering $K^L_u < K^M_u < K^H_u$ (Lemma OA7) is part of the conclusion. $K \ge 0$ because $K$ is a fixed cost. Equilibria follow the tie-breaking rule of p. 10 (a buyer indifferent between auditing and not auditing does not audit), without which parts 2–4 fail at $K = K^M_u$ and $K = K^H_u$. The interior-effort assumption of p. 10 is encoded as the single hypothesis $\hat e_I < 1$ on the explicit formula (2).
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Proposition 2, pp. 11–12; proof p. ec10 (PDF 38)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem proposition_2 (P : Params) (hβ : 0 < P.β) (hint : eHatI P < 1) :
    ∃ KL KM KH : ℝ, KL < KM ∧ KM < KH ∧
      ∀ K : ℝ, 0 ≤ K →
        (K < KL → EqSet P K = {((eStarI P, 0), (eStarI P, 0))}) ∧
        (KL ≤ K → K < KM → EqSet P K =
          {((eStarI P, 0), (eStarI P, 0)), ((eHatI P, 0), (0, 0)), ((0, 0), (eHatI P, 0))}) ∧
        (KM ≤ K → K < KH → EqSet P K = {((eHatI P, 0), (0, 0)), ((0, 0), (eHatI P, 0))}) ∧
        (KH ≤ K → EqSet P K = {((0, 0), (0, 0))}) := by sorry

end SupplierAudit.Competition
