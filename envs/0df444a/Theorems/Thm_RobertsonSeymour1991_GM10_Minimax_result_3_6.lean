-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_3_6
-- name    : RobertsonSeymour1991.GM10.Minimax.result_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:54.555179+00:00
-- url     : https://prove2.me/theorems/f24dcec1-c54c-4189-86ba-a372e6f1f736
-- title:
--   (3.6), p. 163 — an exact tree-labelling with no leaf label equal to E
-- statement:
--   Let $E$ be a finite set, $\kappa$ a connectivity function on $E$ and $\mathcal A$ a set of efficient subsets of $E$. If there is an exact tree-labelling over $\mathcal A$, then either $E=\emptyset$, or $E\in\mathcal A$, or there is an exact tree-labelling $(T,\alpha)$ over $\mathcal A$ such that
--
--   $$\alpha(v,e)\ne E\quad\text{for each leaf }v\text{ of }T\text{ and incident edge }e.$$
--
--   It ensures that every leaf of the tree-labelling carries one element of $\mathcal A$, which is used to build a branch-decomposition in claim (2) of the proof of (4.3).
--
--   **Formalization Note** The ground set $E$ is a finite type and subsets are `Set E`, with $E-X$ written as the complement. The hypotheses that $E$ is finite, that $\kappa$ is a connectivity function and that every member of $\mathcal A$ is efficient are the standing assumptions of §3 (p. 159), not additional ones. A tree-labelling stores the ternary tree on `Fin n` and the label of the incidence $(u,e)$, $e=uw$, as `α u w`; only adjacent pairs are ever used.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 163, (3.6)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias

namespace RobertsonSeymour1991.GM10.Minimax

/-- (3.6), p. 163: if there is an exact tree-labelling over `𝒜`, then either `E = ∅`, or `E ∈ 𝒜`, or there
is an exact tree-labelling `(T, α)` over `𝒜` with `α(v, e) ≠ E` for each leaf `v` and incident edge `e`. -/
theorem result_3_6 {E : Type} [Finite E] (κ : Set E → ℤ) (hκ : IsConnectivityFunction κ)
    (𝒜 : Set (Set E)) (h𝒜 : ∀ X ∈ 𝒜, κ X ≤ 0) :
    (∃ (n : ℕ) (L : TreeLabelling κ 𝒜 n), L.IsExact) →
      (Set.univ : Set E) = ∅ ∨ Set.univ ∈ 𝒜 ∨
        ∃ (n : ℕ) (L : TreeLabelling κ 𝒜 n), L.IsExact ∧
          ∀ v w : Fin n, L.T.Adj v w → (L.T.neighborSet v).ncard = 1 → L.α v w ≠ Set.univ := by sorry

end RobertsonSeymour1991.GM10.Minimax
