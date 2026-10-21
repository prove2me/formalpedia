-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_11
-- name    : UnsplitCVRP.Combinatorial.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:18.936113+00:00
-- url     : https://prove2.me/theorems/baff87ce-1817-48f6-8d81-2070fa29857d
-- title:
--   Lemma 11, p. 8 — all loops bound the matching cost
-- statement:
--   At threshold $\delta=1/3$, matching each big client $v$ to its own loop costs $2c(r,v)$. Consequently the minimum auxiliary matching cost satisfies
--   $$
--   \operatorname{cost}(M)\le
--     \mathcal D'_{\rm big}:=\sum_{v\text{ big}}2c(r,v).
--   $$
--   This is the second matching bound used in the final average of Algorithm 1's two branch costs.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 8, Lemma 11

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Lemma 11, p. 8: matching all big clients to themselves is feasible. -/
theorem lemma_11 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) :
    matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) ≤
      radialCount c (bigIn d (1 / 3 : ℝ) (clients n)) := by sorry

end UnsplitCVRP.Combinatorial
