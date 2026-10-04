-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_partition_univ_iff_indecomposable
-- name    : TheoryOfGames.Decomposition.partition_univ_iff_indecomposable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:38:20.694983+00:00
-- url     : https://prove2.me/theorems/fec73891-d478-4b62-9075-5933a8f8cec5
-- title:
--   (43:K) — Π_Γ consists of I iff the game is indecomposable
-- statement:
--   Let $I$ be a nonempty finite set of players, $v$ satisfy (42:6:a)–(42:6:c), and let $\Pi_\Gamma$ be the system of minimal splitting sets. Then
--   $$\Pi_\Gamma = \{I\} \iff \Gamma \text{ is indecomposable},$$
--   where indecomposable means that $\ominus$ and $I$ are the only splitting sets (43.3.1).
--
--   This is the other extreme case: the coarsest possible decomposition partition.
--
--   **Formalization Note** The nonemptiness of $I$ (the book's $n \geqq 1$) is an explicit hypothesis `[Nonempty ι]`: for $I = \ominus$ the game would be indecomposable while $\Pi_\Gamma$ is empty.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 357, 43.4.1, (43:K); p. 354, 43.3.1

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:K), 43.4.1: `Π_Γ` consists of `I` if and only if the game `Γ` is indecomposable. The set of
players `I` is nonempty (`n ≥ 1`), as throughout the book. -/
theorem partition_univ_iff_indecomposable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    decompositionPartition v = {Finset.univ} ↔ IsIndecomposable v := by sorry

end TheoryOfGames.Decomposition
