-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_3_5
-- name    : RobertsonSeymour1991.GM10.Minimax.result_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:01.831155+00:00
-- url     : https://prove2.me/theorems/a8b66cac-b71c-4eb9-b09c-bdd577b7dda0
-- title:
--   (3.5), p. 163 — no bias ⇔ a tree-labelling ⇔ an exact tree-labelling
-- statement:
--   Let $E$ be a finite set, $\kappa$ a connectivity function on $E$ and $\mathcal A$ a set of efficient subsets of $E$. The following are equivalent:
--
--   1. there is no bias extending $\mathcal A$;
--   2. there is a tree-labelling over $\mathcal A$;
--   3. there is an exact tree-labelling over $\mathcal A$.
--
--   This is the abstract minimax theorem for connectivity functions from which the tangle/branch-width duality (4.3) is deduced.
--
--   **Formalization Note** The ground set $E$ is a finite type and subsets are `Set E`, with $E-X$ written as the complement. The hypotheses that $E$ is finite, that $\kappa$ is a connectivity function and that every member of $\mathcal A$ is efficient are the standing assumptions of §3 (p. 159), not additional ones. A tree-labelling stores the ternary tree on `Fin n` and the label of the incidence $(u,e)$, $e=uw$, as `α u w`; only adjacent pairs are ever used. The equivalence is stated with `List.TFAE`.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 163, (3.5)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias

namespace RobertsonSeymour1991.GM10.Minimax

/-- (3.5), p. 163: the following are equivalent: (i) there is no bias extending `𝒜`; (ii) there is a
tree-labelling over `𝒜`; (iii) there is an exact tree-labelling over `𝒜`. -/
theorem result_3_5 {E : Type} [Finite E] (κ : Set E → ℤ) (hκ : IsConnectivityFunction κ)
    (𝒜 : Set (Set E)) (h𝒜 : ∀ X ∈ 𝒜, κ X ≤ 0) :
    List.TFAE [¬ ∃ ℬ : Set (Set E), IsBias κ ℬ ∧ 𝒜 ⊆ ℬ,
      ∃ n : ℕ, Nonempty (TreeLabelling κ 𝒜 n),
      ∃ (n : ℕ) (L : TreeLabelling κ 𝒜 n), L.IsExact] := by sorry

end RobertsonSeymour1991.GM10.Minimax
