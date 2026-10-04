-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_partialOrdering_conditionG_of_finite
-- name    : TheoryOfGames.Acyclic.partialOrdering_conditionG_of_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:50:52.21915+00:00
-- url     : https://prove2.me/theorems/96141268-8fd4-4722-a0d9-e6966d5a8f19
-- title:
--   (65:I) — a finite partially ordered D fulfills (65:G)
-- statement:
--   Let $\mathcal S$ be a partial ordering of the set $D$ (conditions (65:B:a), (65:B:b)). If $D$ is finite, then $D$ fulfills condition (65:G):
--
--   $$\forall y \in D:\ y \notin D^m \implies \exists x \in D^m \text{ with } x\mathcal S y,$$
--
--   where $D^m$ is the set of (relative) maxima of $D$.
--
--   Together with (65:H) this shows that a finite partially ordered set has exactly one solution, the set of its maxima; it is the finite-case step for partial orderings that §65.7 later generalizes to acyclic relations.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 593, 65.5.2, (65:I)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_PartialOrdering

namespace TheoryOfGames.Acyclic

/-- (65:I), p. 593: let `S` be a partial ordering of `D` (65.5.1). If `D` is finite, then it
fulfills the condition (65:G): every `y` in `D` that is not a maximum of `D` has a maximum `x`
of `D` with `x S y`. -/
theorem partialOrdering_conditionG_of_finite {α : Type*} (D : Set α) (S : α → α → Prop)
    (hS : IsPartialOrdering D S) (hD : D.Finite) :
    ConditionG D S := by sorry

end TheoryOfGames.Acyclic
