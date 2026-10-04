-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_partialOrdering_isSolution_iff
-- name    : TheoryOfGames.Acyclic.partialOrdering_isSolution_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:53:29.244697+00:00
-- url     : https://prove2.me/theorems/49762c65-af68-46ec-8004-de498c3918c7
-- title:
--   (65:H) — for a partial ordering, the solution is the set of all maxima, provided (65:G) holds
-- statement:
--   Let $\mathcal S$ be a partial ordering of an arbitrary set $D$ (finite or not). Then for every set $V$:
--
--   $$V \text{ is a solution (in } D \text{ for } \mathcal S) \iff D \text{ fulfills (65:G) and } V = D^m,$$
--
--   where $D^m$ is the set of all (relative) maxima of $D$ and (65:G) is the condition that every non-maximal $y \in D$ is dominated, $x\mathcal S y$, by some maximum $x$.
--
--   Consequently a partially ordered $D$ has no solution if (65:G) fails and exactly one solution if it holds, even though its relative maxima need not be unique.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 593, 65.5.1, (65:H)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_PartialOrdering

namespace TheoryOfGames.Acyclic

/-- (65:H), p. 593: let `S` be a partial ordering of `D` (65.5.1). Then `V` is a solution
(in `D` for `S`) if and only if (65:G) is fulfilled (by `D` and `S`) and `V` is the set of all
(relative) maxima of `D`. `D` is an arbitrary set, finite or not. -/
theorem partialOrdering_isSolution_iff {α : Type*} (D : Set α) (S : α → α → Prop)
    (hS : IsPartialOrdering D S) (V : Set α) :
    IsSolution D S V ↔ ConditionG D S ∧ V = maxima D S := by sorry

end TheoryOfGames.Acyclic
