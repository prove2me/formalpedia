-- Prove2me | Theorems.Thm_SBMThreshold_Main_claim_4_3
-- name    : SBMThreshold.Main.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:10.729977+00:00
-- url     : https://prove2.me/theorems/decf5700-7a68-4b90-b65d-e5d556d5b111
-- title:
--   Claim 4.3, p. 17 — a path visits k_n(γ)+1 vertices and k_n(γ)+k_r(γ) edges
-- statement:
--   Let $\gamma=(u_0,\dots,u_k)$ be a path (consecutive vertices distinct) and let $k_n(\gamma)$ and $k_r(\gamma)$ be its numbers of new and returning steps (Definition 4.1). Then
--   $$
--   |V(\gamma)|=k_n(\gamma)+1,\qquad |E(\gamma)|=k_n(\gamma)+k_r(\gamma).
--   $$
--
--   Every new step adds one vertex and one edge, a returning step adds one edge, and an old step adds neither. The claim converts the edge-type counts into the sizes of the path's vertex and edge sets, which is how the path counts of §4 are turned into powers of $n$.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 17, Claim 4.3

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Claim 4.3 (p. 17): a path visits `k_n(γ) + 1` vertices and `k_n(γ) + k_r(γ)` edges. -/
theorem claim_4_3 {n k : ℕ} (γ : Fin (k + 1) → Fin n) (hγ : IsPath γ) :
    (pathVertices γ).card = kNew γ + 1 ∧ (pathEdges γ).card = kNew γ + kRet γ := by sorry

end SBMThreshold.Main
