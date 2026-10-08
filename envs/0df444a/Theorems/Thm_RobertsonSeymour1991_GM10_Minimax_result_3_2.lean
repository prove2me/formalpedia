-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_3_2
-- name    : RobertsonSeymour1991.GM10.Minimax.result_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:08.521177+00:00
-- url     : https://prove2.me/theorems/b43fd8ea-2b78-4142-898d-24b08d518c91
-- title:
--   (3.2), p. 160 — a tree-labelling over 𝒜 can be made exact on the same tree
-- statement:
--   Let $E$ be a finite set, $\kappa$ a connectivity function on $E$ and $\mathcal A$ a set of efficient subsets of $E$. If $(T,\alpha)$ is a tree-labelling over $\mathcal A$, then there is an exact tree-labelling $(T,\alpha')$ over $\mathcal A$ using the same tree $T$.
--
--   Exactness is what turns a tree-labelling into a branch-decomposition in claim (2) of the proof of (4.3).
--
--   **Formalization Note** The ground set $E$ is a finite type and subsets are `Set E`, with $E-X$ written as the complement. The hypotheses that $E$ is finite, that $\kappa$ is a connectivity function and that every member of $\mathcal A$ is efficient are the standing assumptions of §3 (p. 159), not additional ones. A tree-labelling stores the ternary tree on `Fin n` and the label of the incidence $(u,e)$, $e=uw$, as `α u w`; only adjacent pairs are ever used. "The same tree" means the same vertex count `n` and the same graph `T`.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 160, (3.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias

namespace RobertsonSeymour1991.GM10.Minimax

/-- (3.2), p. 160: if there is a tree-labelling over `𝒜` then there is an exact tree-labelling over `𝒜`,
using the same tree. -/
theorem result_3_2 {E : Type} [Finite E] (κ : Set E → ℤ) (hκ : IsConnectivityFunction κ)
    (𝒜 : Set (Set E)) (h𝒜 : ∀ X ∈ 𝒜, κ X ≤ 0) (n : ℕ) (L : TreeLabelling κ 𝒜 n) :
    ∃ L' : TreeLabelling κ 𝒜 n, L'.T = L.T ∧ L'.IsExact := by sorry

end RobertsonSeymour1991.GM10.Minimax
