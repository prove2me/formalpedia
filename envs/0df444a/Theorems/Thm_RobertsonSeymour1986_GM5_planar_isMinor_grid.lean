-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_planar_isMinor_grid
-- name    : RobertsonSeymour1986.GM5.planar_isMinor_grid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:56:29.461824+00:00
-- url     : https://prove2.me/theorems/e7015d90-d199-4351-8397-bc88ea9f286c
-- title:
--   Every planar graph is a minor of an even grid of size at least $6$
-- statement:
--   Let $H$ be a finite planar graph. Then there is an even integer $\theta\ge 6$ such that
--
--   $$H \text{ is isomorphic to a minor of the } \theta\text{-grid}.$$
--
--   This fact makes the quantity $\theta(H)$ well defined: the smallest even $\theta\ge 6$ with this property. The main theorem (2.1) bounds the tree-width of graphs excluding $H$ in terms of $\theta(H)$.
--
--   **Formalization Note** $H$ is a finite simple graph and planarity is the existence of a plane drawing.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 2, p. 94 (PDF p. 3), unnumbered statement before the definition of θ(H) (proof cited to [1, 12]); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace RobertsonSeymour1986.GM5

/-- Every finite planar graph is a minor of an even grid of size at least 6.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 2, p. 94 (PDF p. 3), unnumbered: "For any planar graph H there is an even value of
θ ≥ 6 such that H is isomorphic to a minor of the θ-grid. (This is easy to see, but for a proof see
[1, 12].)" This is what makes θ(H) in (2.1) well defined.

**Formalization Note** `H` is a finite simple graph (the paper allows loops and multiple edges;
see the goal theorem). "Isomorphic to a minor" is `IsMinor` (branch-set model on `H`'s own vertex
type). -/
theorem planar_isMinor_grid {W : Type} [Fintype W] (H : SimpleGraph W) (hH : IsPlanar H) :
    ∃ θ : ℕ, Even θ ∧ 6 ≤ θ ∧ IsMinor H (grid θ) := by sorry

end RobertsonSeymour1986.GM5
