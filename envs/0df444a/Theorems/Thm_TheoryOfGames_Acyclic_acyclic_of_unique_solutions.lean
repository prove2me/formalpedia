-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_acyclic_of_unique_solutions
-- name    : TheoryOfGames.Acyclic.acyclic_of_unique_solutions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:07:39.151819+00:00
-- url     : https://prove2.me/theorems/fc4f7880-9e41-41cf-b98d-42559bcfcbc3
-- title:
--   (65:Z) — unique solutions in every E ⊆ D require acyclicity
-- statement:
--   Let $D$ be an arbitrary set (finite or not) and $\mathcal S$ a relation on $D$. If for each $E \subseteq D$ there exists a unique solution in $E$ for $\mathcal S$ — a unique set $V$ with $V = \{y \in E : x\mathcal S y \text{ for no } x \in V\}$ — then $\mathcal S$ is acyclic on $D$:
--
--   $$\bigl(\forall E \subseteq D\ \exists!\, V:\ V \text{ is a solution in } E \text{ for } \mathcal S\bigr) \implies \mathcal S \text{ is acyclic on } D.$$
--
--   Combined with (65:X) applied to every subset of a finite $D$ (the sufficiency half, (65:Y)), this characterizes the finite sets on which every subset has a unique solution: exactly those on which $\mathcal S$ is acyclic.
--
--   **Formalization Note** The relation on $E$ is the restriction of $\mathcal S$; `IsSolution E S V` quantifies only over elements of $E$, which is that restriction.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 601, 65.8.2, (65:Z)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity

namespace TheoryOfGames.Acyclic

/-- (65:Z), p. 601: in order that there exist for each `E ⊆ D` a unique solution (in `E` for
`S`) acyclicity is necessary. `D` is an arbitrary set, finite or not. -/
theorem acyclic_of_unique_solutions {α : Type*} (D : Set α) (S : α → α → Prop)
    (h : ∀ E : Set α, E ⊆ D → ∃! V : Set α, IsSolution E S V) :
    IsAcyclic D S := by sorry

end TheoryOfGames.Acyclic
