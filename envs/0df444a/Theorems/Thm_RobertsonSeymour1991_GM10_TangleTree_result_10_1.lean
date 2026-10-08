-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TangleTree_result_10_1
-- name    : RobertsonSeymour1991.GM10.TangleTree.result_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:35.950583+00:00
-- url     : https://prove2.me/theorems/45fe15be-54b0-459c-bfc2-e98fb2ef4c13
-- title:
--   (10.1), p. 180 — two tangles are distinguished by a separation iff neither contains the other
-- statement:
--   Let $\mathcal T_1$, $\mathcal T_2$ be tangles in a finite hypergraph $G$ (of orders $\theta_1,\theta_2$). Call them **indistinguishable** if $\mathcal T_1\subseteq\mathcal T_2$ or $\mathcal T_2\subseteq\mathcal T_1$. Then exactly one of the following holds:
--   $$\exists\ \text{a separation } (A,B) \text{ of } G \text{ with } (A,B)\in\mathcal T_1,\ (B,A)\in\mathcal T_2,\qquad\text{or}\qquad \mathcal T_1,\mathcal T_2 \text{ are indistinguishable}.$$
--
--   Thus two tangles are either truncations of one another or are told apart by a single separation, which is what makes "distinction" a meaningful notion.
--
--   **Formalization Note** "Either … or … and not both" is the exclusive or `Xor`. The page opens §10 with "tangles in a graph $G$"; the statement is made here for hypergraphs, since (10.3) and (10.4) apply it to hypergraphs and the proof uses no bound on edge sizes. The orders $\theta_1,\theta_2$ are arbitrary and independent.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 180, (10.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TieBreaker

namespace RobertsonSeymour1991.GM10.TangleTree

/-- (10.1), p. 180. Let `𝒯₁`, `𝒯₂` be tangles in the hypergraph `G` (of any orders `θ₁`, `θ₂`).
Either there is a separation of `G` which distinguishes `𝒯₁` from `𝒯₂`, or `𝒯₁`, `𝒯₂` are
indistinguishable (`𝒯₁ ⊆ 𝒯₂` or `𝒯₂ ⊆ 𝒯₁`), and not both. -/
theorem result_10_1 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (θ₁ θ₂ : ℕ) (𝒯₁ 𝒯₂ : Set (G.Sub × G.Sub))
    (h₁ : G.IsTangle θ₁ 𝒯₁) (h₂ : G.IsTangle θ₂ 𝒯₂) :
    Xor (∃ A B : G.Sub, Hypergraph.IsSeparation A B ∧ Hypergraph.Distinguishes 𝒯₁ 𝒯₂ A B)
      (𝒯₁ ⊆ 𝒯₂ ∨ 𝒯₂ ⊆ 𝒯₁) := by sorry

end RobertsonSeymour1991.GM10.TangleTree
