-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TangleTree_result_10_2
-- name    : RobertsonSeymour1991.GM10.TangleTree.result_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:58.613035+00:00
-- url     : https://prove2.me/theorems/0e37712b-7a73-450d-b8fb-2e1feb20dde5
-- title:
--   (10.2), p. 181 — the (𝒯₁, 𝒯₂)-distinction is doubly λ-robust
-- statement:
--   Let $\mathcal T_1$, $\mathcal T_2$ be distinguishable tangles in a finite hypergraph $G$ (neither $\mathcal T_1\subseteq\mathcal T_2$ nor $\mathcal T_2\subseteq\mathcal T_1$), let $\lambda$ be a tie-breaker in $G$, and let $(A,B)$ be the $(\mathcal T_1,\mathcal T_2)$-distinction. Then
--   $$(A,B)\ \text{is doubly } \lambda\text{-robust}.$$
--
--   Combined with (9.4), it shows that the distinctions between any family of pairwise distinguishable tangles form a laminar set.
--
--   **Formalization Note** The result is stated for every separation satisfying `IsDistinction` (minimum $\lambda$-order among the separations distinguishing $\mathcal T_1$ from $\mathcal T_2$); by the first tie-breaker axiom there is exactly one. As for (10.1), the statement is for hypergraphs rather than the graphs named at the start of §10.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 181, (10.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TieBreaker

namespace RobertsonSeymour1991.GM10.TangleTree

/-- (10.2), p. 181. If `𝒯₁`, `𝒯₂` are distinguishable tangles in `G` and `λ` is a tie-breaker,
the `(𝒯₁, 𝒯₂)`-distinction is doubly `λ`-robust. -/
theorem result_10_2 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (θ₁ θ₂ : ℕ) (𝒯₁ 𝒯₂ : Set (G.Sub × G.Sub))
    (h₁ : G.IsTangle θ₁ 𝒯₁) (h₂ : G.IsTangle θ₂ 𝒯₂) (hd : ¬ 𝒯₁ ⊆ 𝒯₂ ∧ ¬ 𝒯₂ ⊆ 𝒯₁)
    {Λ : Type} [LinearOrder Λ] (lam : G.Sub × G.Sub → Λ) (hlam : G.IsTieBreaker lam)
    (A B : G.Sub) (hAB : Hypergraph.IsDistinction lam 𝒯₁ 𝒯₂ A B) :
    Hypergraph.IsDoublyRobust lam A B := by sorry

end RobertsonSeymour1991.GM10.TangleTree
