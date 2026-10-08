-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_3_1
-- name    : RobertsonSeymour1991.GM10.Minimax.result_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:15.669182+00:00
-- url     : https://prove2.me/theorems/c7ad621a-f2b2-4c2d-9d2c-8e6d5743c3fa
-- title:
--   (3.1), p. 160 — a bias extending 𝒜 excludes every tree-labelling over 𝒜
-- statement:
--   Let $E$ be a finite set, $\kappa$ a connectivity function on $E$ and $\mathcal A$ a set of efficient subsets of $E$. If there is a bias extending $\mathcal A$, then there is no tree-labelling over $\mathcal A$:
--
--   $$\bigl(\exists\,\mathcal B\text{ bias},\ \mathcal A\subseteq\mathcal B\bigr)\ \Longrightarrow\ \neg\bigl(\exists\text{ tree-labelling over }\mathcal A\bigr).$$
--
--   This is the easy direction of the abstract minimax lemma (3.5).
--
--   **Formalization Note** The ground set $E$ is a finite type and subsets are `Set E`, with $E-X$ written as the complement. The hypotheses that $E$ is finite, that $\kappa$ is a connectivity function and that every member of $\mathcal A$ is efficient are the standing assumptions of §3 (p. 159), not additional ones. A tree-labelling stores the ternary tree on `Fin n` and the label of the incidence $(u,e)$, $e=uw$, as `α u w`; only adjacent pairs are ever used.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 160, (3.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias

namespace RobertsonSeymour1991.GM10.Minimax

/-- (3.1), p. 160: if there is a bias extending `𝒜` then there is no tree-labelling over `𝒜`. -/
theorem result_3_1 {E : Type} [Finite E] (κ : Set E → ℤ) (hκ : IsConnectivityFunction κ)
    (𝒜 : Set (Set E)) (h𝒜 : ∀ X ∈ 𝒜, κ X ≤ 0) :
    (∃ ℬ : Set (Set E), IsBias κ ℬ ∧ 𝒜 ⊆ ℬ) → ¬ ∃ n : ℕ, Nonempty (TreeLabelling κ 𝒜 n) := by sorry

end RobertsonSeymour1991.GM10.Minimax
