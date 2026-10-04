-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_V0_isSolution
-- name    : TheoryOfGames.Acyclic.V0_isSolution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:04:17.837114+00:00
-- url     : https://prove2.me/theorems/96d6b2bf-de6f-44ad-aaec-2033693acfb9
-- title:
--   (65:W) — V₀ is a solution for an acyclic relation on a finite D
-- statement:
--   Assume the standing hypotheses of 65.7.1: $D$ is finite and $\mathcal S$ is acyclic on $D$. Then the set $V_0 = B_1 \cup \cdots \cup B_{i_0-1}$ of (65:2) is a solution (in $D$ for $\mathcal S$):
--
--   $$V_0 = \{\, y \in D : x\mathcal S y \text{ for no } x \in V_0 \,\}.$$
--
--   This is the existence half of (65:X).
--
--   **Formalization Note** `V0 D S` is the union of all stages $B_i$ of 65.7.1, which equals $B_1 \cup \cdots \cup B_{i_0-1}$ because $B_i = \ominus$ for $i \ge i_0$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 599, 65.7.2, (65:W)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity
import Definitions.Def_TheoryOfGames_Acyclic_Construction

namespace TheoryOfGames.Acyclic

/-- (65:W), p. 599: under the standing assumptions of 65.7.1 (`D` finite, `S` acyclic on `D`),
`V₀` of (65:2) is a solution (in `D` for `S`). -/
theorem V0_isSolution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    IsSolution D S (V0 D S) := by sorry

end TheoryOfGames.Acyclic
