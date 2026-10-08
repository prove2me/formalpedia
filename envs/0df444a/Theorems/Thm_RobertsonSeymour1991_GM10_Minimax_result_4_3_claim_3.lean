-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_4_3_claim_3
-- name    : RobertsonSeymour1991.GM10.Minimax.result_4_3_claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:02:20.854261+00:00
-- url     : https://prove2.me/theorems/24afa58e-457a-4167-8975-51ec02fd1c86
-- title:
--   (4.3), proof, claim (3), p. 166 — with γ(G) > 0: for all k ≥ γ(G), G has a tangle of order k + 1 iff k < β(G)
-- statement:
--   Let $G$ be a hypergraph with $\gamma(G)>0$. For every integer $k\ge\gamma(G)$,
--
--   $$G\text{ has a tangle of order }k+1\iff k<\beta(G).$$
--
--   This is the characterization from which $\max(\beta(G),\gamma(G))=\theta(G)$ is read off.
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. The hypothesis $\gamma(G)>0$ is the standing assumption of the proof of (4.3) from p. 165 on; "for all $k\ge\gamma(G)$" is the claim's own quantifier, over natural numbers $k$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 166, proof of (4.3), claim (3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition

namespace RobertsonSeymour1991.GM10.Minimax

/-- (4.3), proof, claim (3), p. 166. Context: `γ(G) > 0`. For all `k ≥ γ(G)`, `G` has a tangle of order
`k + 1` if and only if `k < β(G)`. -/
theorem result_4_3_claim_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (hγ : 0 < G.maxEdgeSize) :
    ∀ k : ℕ, G.maxEdgeSize ≤ k →
      ((∃ 𝒯 : Set (G.Sub × G.Sub), G.IsTangle (k + 1) 𝒯) ↔ k < branchWidth G) := by sorry

end RobertsonSeymour1991.GM10.Minimax
