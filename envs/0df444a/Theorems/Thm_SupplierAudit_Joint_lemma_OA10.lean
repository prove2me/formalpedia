-- Prove2me | Theorems.Thm_SupplierAudit_Joint_lemma_OA10
-- name    : SupplierAudit.Joint.lemma_OA10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:28.498821+00:00
-- url     : https://prove2.me/theorems/b3abd719-906c-4d27-82ea-df32e8012b44
-- title:
--   Lemma OA10 — auditing $S_c$ and one independent supplier beats auditing both independent suppliers
-- statement:
--   Consider the joint-auditing coalition with competing buyers ($0<\beta\le1$), in the Sec. 4.3 scenario $\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M)$. Let $\Pi^b(e_{c1},e_{cc},e_{c2})$ be its aggregate expected profit. For every fixed cost $K\ge0$ and all efforts $y,z\in[0,1]$, there are efforts $y',z'\in[0,1]$ with
--   $$\Pi^b(y,0,z)\le\Pi^b(y',z',0).$$
--
--   That is, whatever the coalition earns by auditing both independent suppliers, it earns at least as much by auditing the common supplier together with one independent supplier. With Lemma OA9, this reduces the coalition's choice to three candidate plans: audit $S_1$ and $S_c$, audit $S_c$ only, or audit nothing.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma OA10, p. ec11 (PDF 39), proof p. ec12 (PDF 40); scenario of Sec. 4.3, p. 13

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Lemma OA10, p. ec11: jointly auditing the common supplier and an independent supplier is at
least as good as jointly auditing both independent suppliers. -/
theorem lemma_OA10 (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) (K : ℝ) (hK : 0 ≤ K) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      ∃ y' ∈ Set.Icc (0 : ℝ) 1, ∃ z' ∈ Set.Icc (0 : ℝ) 1,
        aggProfit P K (y, 0, z) ≤ aggProfit P K (y', z', 0) := by sorry

end SupplierAudit.Joint
