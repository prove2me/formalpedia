-- Prove2me | Theorems.Thm_SupplierAudit_Joint_lemma_OA9
-- name    : SupplierAudit.Joint.lemma_OA9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:30.844536+00:00
-- url     : https://prove2.me/theorems/d1b54552-51dc-4f00-8479-0a10586801d5
-- title:
--   Lemma OA9 — the coalition prefers auditing $S_c$ to one independent supplier, and to no audit when $K<\hat K$
-- statement:
--   Consider the joint-auditing coalition with competing buyers ($0<\beta\le1$), in the Sec. 4.3 scenario $\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M)$. Let $\Pi^b(e_{c1},e_{cc},e_{c2})$ be its aggregate expected profit, and let
--   $$\hat K=\max_{y\in[0,1]}\Pi^b(0,y,0)\big|_{K=0}-\Pi^b(0,0,0).$$
--   Then:
--
--   1. for every fixed cost $K\ge0$ and every effort $y\in[0,1]$ there is an effort $z\in[0,1]$ with $\Pi^b(y,0,0)\le\Pi^b(0,z,0)$ and $\Pi^b(0,0,y)\le\Pi^b(0,z,0)$, so auditing the common supplier is at least as good as auditing either independent supplier;
--   2. $\hat K\ge0$;
--   3. if $0\le K<\hat K$, there is an effort $y\in(0,1]$ with
--   $$\Pi^b(0,y,0)>\Pi^b(0,0,0),$$
--   so auditing the common supplier is strictly better than auditing no supplier.
--
--   This lemma is the first step of the case analysis behind Proposition 3: among single audits the coalition always prefers the common supplier.
--
--   **Formalization Note** The paper's "there exists a threshold $\hat K$" is stated with the threshold defined in its proof.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma OA9 and its proof, p. ec11 (PDF 39); scenario of Sec. 4.3, p. 13

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Lemma OA9, p. ec11: under joint auditing, auditing the common supplier is at least as good as
auditing one independent supplier; and with `K̂` as defined in its proof, `K̂ ≥ 0` and for
`0 ≤ K < K̂` some joint audit of the common supplier is strictly better than auditing no supplier. -/
theorem lemma_OA9 (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) :
    (∀ K : ℝ, 0 ≤ K → ∀ y ∈ Set.Icc (0 : ℝ) 1, ∃ z ∈ Set.Icc (0 : ℝ) 1,
        aggProfit P K (y, 0, 0) ≤ aggProfit P K (0, z, 0) ∧
        aggProfit P K (0, 0, y) ≤ aggProfit P K (0, z, 0)) ∧
    0 ≤ Khat P ∧
    ∀ K : ℝ, 0 ≤ K → K < Khat P →
      ∃ y ∈ Set.Ioc (0 : ℝ) 1, aggProfit P K (0, 0, 0) < aggProfit P K (0, y, 0) := by sorry

end SupplierAudit.Joint
