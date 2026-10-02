-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_eq_V0_of_isSolution
-- name    : TheoryOfGames.Acyclic.eq_V0_of_isSolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:02:31.079505+00:00
-- url     : https://prove2.me/theorems/50a74906-19fa-45c4-b971-c9cfff315433
-- title:
--   (65:V) — every solution for an acyclic relation on a finite D equals V₀
-- statement:
--   Assume the standing hypotheses of 65.7.1: $D$ is finite and $\mathcal S$ is acyclic on $D$. Let $V_0 = B_1 \cup \cdots \cup B_{i_0-1}$ be the set of (65:2), built by the construction of 65.7.1. If $V$ is a solution (in $D$ for $\mathcal S$), i.e. $V = \{y \in D : x\mathcal S y \text{ for no } x \in V\}$, then
--
--   $$V = V_0.$$
--
--   This is the uniqueness half of (65:X).
--
--   **Formalization Note** `V0 D S` is the union of all stages $B_i$ of 65.7.1, which equals $B_1 \cup \cdots \cup B_{i_0-1}$ because $B_i = \ominus$ for $i \ge i_0$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 599, 65.7.2, (65:V)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity
import Definitions.Def_TheoryOfGames_Acyclic_Construction

namespace TheoryOfGames.Acyclic

/-- (65:V), p. 599: under the standing assumptions of 65.7.1 (`D` finite, `S` acyclic on `D`),
if `V` is a solution (in `D` for `S`), then `V = V₀`, the set of (65:2). -/
theorem eq_V0_of_isSolution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) (V : Set α) (hV : IsSolution D S V) :
    V = V0 D S := by sorry

end TheoryOfGames.Acyclic
