-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_partition_singletons_iff_inessential
-- name    : TheoryOfGames.Decomposition.partition_singletons_iff_inessential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:36:35.330381+00:00
-- url     : https://prove2.me/theorems/a85bab99-bbbb-4cea-897a-a8c6dc4344fe
-- title:
--   (43:J) — Π_Γ is the system of all one-element sets iff the game is inessential
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$, and let $\Pi_\Gamma$ be the system of minimal splitting sets. Then
--   $$\Pi_\Gamma = \{\{k\} : k \in I\} \iff \text{the game is inessential},$$
--   where inessential means (42:F): there are real numbers $\alpha^0_k$ with $v(S) + \sum_{k \in S} \alpha^0_k = 0$ for all $S \subseteq I$.
--
--   This is one of the two extreme cases of the decomposition partition: the finest possible one.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 357, 43.4.1, (43:J); p. 351, (42:F)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:J), 43.4.1: `Π_Γ` is the system of all one-element sets (in `I`) if and only if the game
is inessential. -/
theorem partition_singletons_iff_inessential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    decompositionPartition v = {J : Finset ι | ∃ k : ι, J = {k}} ↔ IsInessential v := by sorry

end TheoryOfGames.Decomposition
