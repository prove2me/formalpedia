-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Grid_result_7_2
-- name    : RobertsonSeymour1991.GM10.Grid.result_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:39.366598+00:00
-- url     : https://prove2.me/theorems/3229b238-e089-4e9c-8c3f-fd50bb4ae0a1
-- title:
--   (7.2), p. 172 — three small sets cannot cover a grid
-- statement:
--   Let $\theta\ge2$ and let $G$ be the $\theta$-grid. If three edge sets cover all of its edges,
--
--   $$X_1\cup X_2\cup X_3=E(G),$$
--
--   then at least one of $X_1,X_2,X_3$ is not small in $G$. Here small means that the edge boundary has fewer than $\theta$ vertices and the set contains no complete row edge set.
--
--   This is the paper's principal lemma for verifying the grid tangle axioms.
--
--   **Formalization Note** $\theta\ge2$ is the standing assumption of §7. The edge sets range over all subsets of the published grid's edge type; union equals `Set.univ`, which is exactly $E(G)$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 172, (7.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_Small

namespace RobertsonSeymour1991.GM10.Grid

theorem result_7_2 (θ : ℕ) (hθ : 2 ≤ θ)
    (X₁ X₂ X₃ : Set (RobertsonSeymour1986.GM5.grid θ).edgeSet)
    (hcover : X₁ ∪ X₂ ∪ X₃ = Set.univ) :
    ¬ (IsSmall θ X₁ ∧ IsSmall θ X₂ ∧ IsSmall θ X₃) := by sorry

end RobertsonSeymour1991.GM10.Grid
