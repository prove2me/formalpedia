-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_4_3_claim_1
-- name    : RobertsonSeymour1991.GM10.Minimax.result_4_3_claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:28.712673+00:00
-- url     : https://prove2.me/theorems/ad1ea175-914d-48c9-a4fe-af6feb161939
-- title:
--   (4.3), proof, claim (1), p. 165 — with γ(G) > 0, k ≥ γ(G), κ = κ₀ − k, 𝒜 = {{e}}: a bias extends 𝒜 iff G has a tangle of order k + 1
-- statement:
--   Let $G$ be a hypergraph with $\gamma(G)>0$, let $k\ge\gamma(G)$, let $E=E(G)$, let $\kappa(X)=\kappa_0(X)-k$ for $X\subseteq E$, where $\kappa_0(X)$ is the number of vertices incident both with an edge in $X$ and with an edge in $E-X$, and let $\mathcal A=\{\{e\}:e\in E(G)\}$. Then
--
--   $$\text{there is a bias extending }\mathcal A\iff G\text{ has a tangle of order }k+1.$$
--
--   It translates tangles into the language of §3.
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. The hypotheses $\gamma(G)>0$ and $k\ge\gamma(G)$, and the choices $\kappa=\kappa_0-k$ and $\mathcal A=\{\{e\}:e\in E(G)\}$, are the context fixed on p. 165 of the proof of (4.3) ("we henceforth assume that $\gamma(G)>0$", "choose $k\ge\gamma(G)$"); they are the paper's, not added. $k$ is a natural number.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 165, proof of (4.3), claim (1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Kappa0

namespace RobertsonSeymour1991.GM10.Minimax

/-- (4.3), proof, claim (1), p. 165. Context: `γ(G) > 0`, `k ≥ γ(G)`, `κ(X) = κ₀(X) − k` and
`𝒜 = {{e} : e ∈ E(G)}`. There is a bias extending `𝒜` if and only if `G` has a tangle of order `k + 1`. -/
theorem result_4_3_claim_1 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (hγ : 0 < G.maxEdgeSize) (k : ℕ) (hk : G.maxEdgeSize ≤ k) :
    (∃ ℬ : Set (Set E), IsBias (fun X : Set E => G.kappa0 X - (k : ℤ)) ℬ ∧ (Set.range (fun e : E => ({e} : Set E))) ⊆ ℬ) ↔
      ∃ 𝒯 : Set (G.Sub × G.Sub), G.IsTangle (k + 1) 𝒯 := by sorry

end RobertsonSeymour1991.GM10.Minimax
