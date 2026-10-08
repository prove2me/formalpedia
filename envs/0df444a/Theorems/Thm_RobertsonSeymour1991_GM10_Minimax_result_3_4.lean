-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_3_4
-- name    : RobertsonSeymour1991.GM10.Minimax.result_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:00.603634+00:00
-- url     : https://prove2.me/theorems/169f7ac6-4530-4cf2-925a-1c65114960fe
-- title:
--   (3.4), p. 162 — no bias extending 𝒜 gives an exact tree-labelling over 𝒜
-- statement:
--   Let $E$ be a finite set, $\kappa$ a connectivity function on $E$ and $\mathcal A$ a set of efficient subsets of $E$. If there is no bias extending $\mathcal A$, then there is an exact tree-labelling over $\mathcal A$.
--
--   This is the hard direction of the abstract minimax lemma (3.5).
--
--   **Formalization Note** The ground set $E$ is a finite type and subsets are `Set E`, with $E-X$ written as the complement. The hypotheses that $E$ is finite, that $\kappa$ is a connectivity function and that every member of $\mathcal A$ is efficient are the standing assumptions of §3 (p. 159), not additional ones. A tree-labelling stores the ternary tree on `Fin n` and the label of the incidence $(u,e)$, $e=uw$, as `α u w`; only adjacent pairs are ever used.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 162, (3.4)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias

namespace RobertsonSeymour1991.GM10.Minimax

/-- (3.4), p. 162: if there is no bias extending `𝒜` then there is an exact tree-labelling over `𝒜`. -/
theorem result_3_4 {E : Type} [Finite E] (κ : Set E → ℤ) (hκ : IsConnectivityFunction κ)
    (𝒜 : Set (Set E)) (h𝒜 : ∀ X ∈ 𝒜, κ X ≤ 0) :
    (¬ ∃ ℬ : Set (Set E), IsBias κ ℬ ∧ 𝒜 ⊆ ℬ) →
      ∃ (n : ℕ) (L : TreeLabelling κ 𝒜 n), L.IsExact := by sorry

end RobertsonSeymour1991.GM10.Minimax
